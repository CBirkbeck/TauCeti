/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic

/-!
# The upper-left unit character of `Δ₀(N)`

An element of `Δ₀(N)` is an integral matrix, upper-triangular modulo `N`, whose upper-left
entry is a unit mod `N`. Reducing that entry gives a map

```
Δ₀(N) → (ZMod N)ˣ
```

which is multiplicative, because the lower-left entry vanishes mod `N` and so the cross term
in the product drops out. This is the `Δ₀(N)` counterpart of Mathlib's `Gamma0Map`, which
takes the *lower-right* entry of an element of `Γ₀(N)`; on `Γ₀(N)` the two are inverse to one
another, since `ad ≡ 1` there.

Composing with `χ : (ZMod N)ˣ →* ℂˣ` gives the twisting character of the `χ`-twisted Hecke
ring. It is **not** an extension of the nebentypus: `Delta0UpperUnit_mapGL` says that on
`Γ₀(N)` the composite `χ ∘ Delta0UpperUnit` restricts to the *inverse* of
`χ ∘ (Gamma0Map N).toHomUnits`, which is the character `modFormCharSpace` is defined by.

The inverse is the convention, not an accident. The twisted double-coset operator *divides*
by the character — each representative contributes `χ(·)⁻¹ • (f ∣[k] ·)` — so the value that
has to be attached to a monoid element is the reciprocal of the one attached to a group
element acting on forms. Reading `Delta0UpperUnit` as an extension of the nebentypus and
dropping the inverse would negate every twist downstream.

## Main definitions

* `HeckeRing.GL2.Delta0UpperUnit`: the monoid homomorphism `Δ₀(N) →* (ZMod N)ˣ`.

## Main results

* `HeckeRing.GL2.Delta0UpperUnit_apply_val`: *any* integral witness computes it. The
  definition has to choose a witness, but the witness is unique, so no consumer needs the
  chosen one.
* `HeckeRing.GL2.mapGL_mem_Delta0`: `Γ₀(N)` lands in `Δ₀(N)`, so the comparison below needs
  no membership hypothesis.
* `HeckeRing.GL2.Delta0UpperUnit_mapGL`: on `Γ₀(N)` it is inverse to `Gamma0Map`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5 (Hecke operators with nebentypus).
* Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck),
  [`HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`](https://github.com/CBirkbeck/AINTLIB) at
  commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, declarations `delta0IntegralMatrix`,
  `delta0UpperUnit` and `delta0NebentypusDeltaChar`. Twelve source declarations are bundled
  here into one `MonoidHom` with a witness-free eliminator; the source states its API against
  a chosen `Classical.choose` witness instead.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn

open scoped MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- The chosen integral witness of an element of `Δ₀(N)`.

`Δ₀(N)`-membership is an existential over integral matrices, so a value-level map out of it
must choose. The choice is harmless: `Delta0_witness_eq` shows the witness is unique, and
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
        -- `Matrix.map_mul` does not fire on the bare function `Int.cast`; it needs the
        -- `RingHom` coercion, as at `Gamma0/DoubleCoset.lean:119`
        have hmap := map_mul (Int.castRingHom ℚ).mapMatrix
          (delta0Witness N g) (delta0Witness N h)
        simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at hmap
        rw [Submonoid.coe_mul, Units.val_mul, delta0Witness_spec N g,
          delta0Witness_spec N h, hmap])]
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

/-- `Γ₀(N)` lands in `Δ₀(N)`: its elements are integral of determinant one, with lower-left
entry divisible by `N` and upper-left entry a unit because `ad ≡ 1`. -/
lemma mapGL_mem_Delta0 (γ : Gamma0 N) :
    (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ) ∈ Delta0 N :=
  Gamma0Image_le_Delta0 N ((mem_Gamma0Image_iff N).mpr ⟨(γ : SL(2, ℤ)), γ.2, rfl⟩)

/-- **On `Γ₀(N)` the upper-left unit inverts `Gamma0Map`.** The determinant is one and the
lower-left entry vanishes mod `N`, so `ad ≡ 1`: the upper-left unit of `γ` viewed in `Δ₀(N)`
is the inverse of the lower-right unit Mathlib's `Gamma0Map` records.

So `Delta0UpperUnit` does **not** extend the nebentypus along `Gamma0Map`; it restricts to the
inverse of it. That is the convention the twisted Hecke ring wants, because the twisted
double-coset operator divides by the character rather than multiplying by it. -/
@[simp] lemma Delta0UpperUnit_mapGL (γ : Gamma0 N) :
    Delta0UpperUnit N ⟨_, mapGL_mem_Delta0 N γ⟩ = ((Gamma0Map N).toHomUnits γ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  ext
  rw [Units.val_mul, Units.val_one,
    Delta0UpperUnit_apply_val N (A := (γ : Matrix (Fin 2) (Fin 2) ℤ))
      (by simp [mapGL_coe_matrix, algebraMap_int_eq]),
    MonoidHom.coe_toHomUnits, Gamma0Map]
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := (γ : SL(2, ℤ)).2
  have hlow : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp γ.2
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (Int.cast : ℤ → ZMod N) hdet
  push_cast at this
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, hlow, mul_zero, sub_zero] at this ⊢
  exact this

end HeckeRing.GL2
