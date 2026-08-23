/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Basic
-- `Matrix.map_mul_intCast`: the entrywise integer cast is multiplicative on matrices.
public import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# The semigroup `Δ₀(N)`

The submonoid `Δ₀(N) ⊆ GL₂(ℚ)` of integral matrices with positive determinant that are
upper-triangular modulo `N` with unit upper-left entry. It is the `Δ` of the Hecke triples of
both `Γ₀(N)` and `Γ₁(N)`, and nothing about it refers to either group, so it lives here rather
than inside one of the two triple modules.

`Δ₀(N)` is the classical semigroup of Miyake, *Modular Forms*, §4.5: integral, of positive
determinant, with `c ≡ 0` and `a` coprime to `N`, the coprimality spelled here as
`IsUnit (a : ZMod N)`. Asking the upper-left entry to be a *unit* rather than `≡ 1` is what
makes `Γ₀(N) ≤ Δ₀(N)`, so that the Hecke ring of `Γ₁(N)` carries the diamond operators
alongside the `T_p`. The smaller classical semigroup `Δ₁(N)`, cut out by `a ≡ 1`, is the
sub-semigroup carrying the `T_p` alone.

Determinants divisible by `N` are deliberately admitted: `diag(1, p)` lies in `Δ₀(N)` even
when `p ∣ N`, where it gives the bad-prime operator `U_p`. Because of this, the whole
determinant-`n` part of `Δ₀(N)` is the full diamond orbit of the classical `T_n`, not `T_n`
itself; an operator defined downstream must be cut out of the `a ≡ 1` part rather than taken
as that entire fibre.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), with `CoprimeDet` and `coprimeDet_iff` from the `CoprimeDet` section of
`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Props.lean` (Chris Birkbeck).

## Main definitions

* `HeckeRing.GL2.Delta0`: the submonoid `Δ₀(N)`.

## Main results

* `HeckeRing.GL2.mem_Delta0_iff`: membership, unfolded.
* `HeckeRing.GL2.CoprimeDet`, `HeckeRing.GL2.coprimeDet_iff`: the elements whose integral
  representative has determinant coprime to `N`, and the fact that one witness decides it.
* `HeckeRing.GL2.Delta0_le_posDetInt`: `Δ₀(N)` consists of integral matrices of positive
  determinant, which is what puts it in the commensurator of `SL₂(ℤ)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- `Δ₀(N)`: integral matrices of positive determinant that are upper-triangular modulo `N`
with unit upper-left entry, i.e. `c ≡ 0 (mod N)` and `a` a unit in `ZMod N`. The unit
condition (rather than `a ≡ 1`) is what makes `Γ₀(N) ≤ Δ₀(N)`. -/
noncomputable def Delta0 : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
      0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧ (N : ℤ) ∣ A 1 0 ∧ IsUnit (A 0 0 : ZMod N)}
  one_mem' := ⟨1, by simp, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨A, hA, hda, hAN, hAunit⟩ ⟨B, hB, hdb, hBN, hBunit⟩
    refine ⟨A * B, ?_, ?_, ?_, ?_⟩
    · ext i j
      simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]
    · simpa [Matrix.det_mul] using mul_pos hda hdb
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hAN _) (dvd_mul_of_dvd_right hBN _)
    · -- the upper-left entry of the product is `a₁a₂` modulo `N`, since `c₂ ≡ 0`
      have hentry : ((A * B) 0 0 : ZMod N) = (A 0 0 : ZMod N) * (B 0 0 : ZMod N) := by
        simp [Matrix.mul_apply, Fin.sum_univ_two,
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hBN]
      rw [hentry]
      exact hAunit.mul hBunit

/-- Membership in `Δ₀(N)`, unfolded. -/
@[simp] lemma mem_Delta0_iff {g : GL (Fin 2) ℚ} :
    g ∈ Delta0 N ↔ ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
        0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧ (N : ℤ) ∣ A 1 0 ∧
          IsUnit (A 0 0 : ZMod N) :=
  Iff.rfl

/-- An element of `Δ₀(N)` has **coprime determinant** when every integral matrix representing
it has determinant coprime to `N`.

Quantifying over all representatives rather than choosing one keeps the predicate free of a
choice; the representative is unique anyway, since `ℤ → ℚ` is injective. -/
def CoprimeDet (g : Delta0 N) : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) →
      Int.gcd A.det N = 1

/-- `CoprimeDet` is decided by any single integral witness: the witness is unique, because the
entrywise cast `ℤ → ℚ` is injective. This is the introduction rule for the definition, whose
universal quantifier only eliminates. -/
lemma coprimeDet_iff {g : Delta0 N} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    CoprimeDet N g ↔ Int.gcd A.det N = 1 := by
  refine ⟨fun h ↦ h A hA, fun h A' hA' ↦ ?_⟩
  have : A' = A := Matrix.map_injective Int.cast_injective (hA'.symm.trans hA)
  exact this ▸ h

/-! ### The upper-left unit character -/

/-- The chosen integral witness of an element of `Δ₀(N)`.

`Δ₀(N)`-membership is an existential over integral matrices, so a value-level map out of it
must choose. The choice is harmless: `delta0Witness_eq` shows the witness is unique, and
`Delta0UpperUnit_apply_val` states the resulting API against an arbitrary witness, so this
definition never escapes into a consumer's proof obligation. -/
private noncomputable def delta0Witness (g : Delta0 N) : Matrix (Fin 2) (Fin 2) ℤ :=
  Classical.choose ((mem_Delta0_iff N).mp g.2)

private lemma delta0Witness_spec (g : Delta0 N) :
    ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (delta0Witness N g).map (Int.cast : ℤ → ℚ) :=
  (Classical.choose_spec ((mem_Delta0_iff N).mp g.2)).1

private lemma delta0Witness_lowerLeft (g : Delta0 N) : (N : ℤ) ∣ delta0Witness N g 1 0 :=
  (Classical.choose_spec ((mem_Delta0_iff N).mp g.2)).2.2.1

private lemma isUnit_delta0Witness_upperLeft (g : Delta0 N) :
    IsUnit ((delta0Witness N g 0 0 : ℤ) : ZMod N) :=
  (Classical.choose_spec ((mem_Delta0_iff N).mp g.2)).2.2.2

/-- The integral witness of an element of `Δ₀(N)` is unique: the entrywise cast `ℤ → ℚ` is
injective, so two witnesses for the same matrix agree. This is the same observation that lets
`CoprimeDet` be decided by a single witness. -/
private lemma delta0Witness_eq {g : Delta0 N} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    delta0Witness N g = A :=
  Matrix.map_injective Int.cast_injective ((delta0Witness_spec N g).symm.trans hA)

/-- **The upper-left unit character of `Δ₀(N)`**, reducing the upper-left entry of an integral
witness modulo `N`. It is multiplicative because the lower-left entry of a `Δ₀(N)` matrix
vanishes mod `N`, killing the cross term in the product. -/
noncomputable def Delta0UpperUnit : Delta0 N →* (ZMod N)ˣ where
  toFun g := (isUnit_delta0Witness_upperLeft N g).unit
  map_one' := by
    ext
    rw [IsUnit.unit_spec, delta0Witness_eq N (A := 1) (by simp)]
    simp
  map_mul' g h := by
    ext
    rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec,
      delta0Witness_eq N (A := delta0Witness N g * delta0Witness N h) (by
        rw [Submonoid.coe_mul, Units.val_mul, delta0Witness_spec N g,
          delta0Witness_spec N h, Matrix.map_mul_intCast])]
    have hzero : ((delta0Witness N g 0 1 * delta0Witness N h 1 0 : ℤ) : ZMod N) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Dvd.dvd.mul_left (delta0Witness_lowerLeft N h) _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul, hzero, add_zero]

/-- **The eliminator.** Any integral witness computes the upper-left unit, so a consumer never
has to reach for the chosen one.

Not `@[simp]`: `A` occurs only in the hypothesis and the right-hand side, so `simp` cannot
infer it — the same reason `diamondOp_apply_of_mem_modFormCharSpace` is not a simp lemma. -/
lemma Delta0UpperUnit_apply_val {g : Delta0 N} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    (Delta0UpperUnit N g : ZMod N) = (A 0 0 : ZMod N) := by
  rw [Delta0UpperUnit, MonoidHom.coe_mk, OneHom.coe_mk, IsUnit.unit_spec,
    delta0Witness_eq N hA]

/-- `Δ₀(N)` consists of integral matrices with positive determinant. -/
lemma Delta0_le_posDetInt : Delta0 N ≤ posDetInt 2 := by
  intro g hg
  obtain ⟨A, hA, hdet, -, -⟩ := (mem_Delta0_iff N).mp hg
  exact (mem_posDetInt_iff 2).mpr ⟨(hasIntEntries_iff 2).mpr ⟨A, hA⟩, hdet⟩

end HeckeRing.GL2
