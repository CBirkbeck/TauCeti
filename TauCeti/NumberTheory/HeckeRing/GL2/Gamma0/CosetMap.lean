/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.Basic
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DoubleCoset

/-!
# Comparing the `Γ₀(N)` and level-one double cosets

**Shimura, Propositions 3.30 and 3.31.** Since `Γ₀(N) ≤ SL₂(ℤ)` and `Δ₀(N) ≤ Δ`, sending
`Γ₀(N) α Γ₀(N)` to `SL₂(ℤ) α SL₂(ℤ)` is well defined on double cosets:

```lean
noncomputable def toLevelOneCoset :
    HeckeCoset (Delta0 N) (Gamma0Image N) (Gamma0Image N) →
      HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)
```

and it is **injective on the cosets whose determinant is coprime to the level**
(`injOn_toLevelOneCoset`). Injectivity is the content: two `Γ₀(N)`-double cosets
with the same level-one double coset are recovered from it by intersecting with `Δ₀(N)`, which
is exactly `doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image`.

This is the injectivity step towards a later good-prime comparison of `R(Γ₀(N), Δ₀(N))` with
the level-one Hecke ring. Neither surjectivity nor compatibility with the Hecke-ring operations
is proved here: this file compares the two *coset types* only.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Props.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), the `cosetMap`
and `shimura_prop_3_31` section. The bespoke `Delta0_inclusion` there is `Submonoid.inclusion`
here, and AINTLIB's `HeckePair` bundle is Mathlib's `HeckeCoset`.

## Main definitions

* `HeckeRing.GL2.CoprimeDet`: an element of `Δ₀(N)` whose integral representative has
  determinant coprime to `N`.
* `HeckeRing.GL2.CoprimeDetCoset`: the same condition on a `Γ₀(N)`-double coset — well defined
  because the coefficients have determinant one, so the determinant is constant on a coset.
* `HeckeRing.GL2.toLevelOneCoset`: the map `Γ₀(N) α Γ₀(N) ↦ SL₂(ℤ) α SL₂(ℤ)`, the `Γ₀`
  specialisation of `HeckeCoset.map`.

## Main results

* `HeckeRing.GL2.toLevelOneCoset_mk`, `HeckeRing.GL2.coprimeDetCoset_mk`: the computation rules
  on a representative.
* `HeckeRing.GL2.injOn_toLevelOneCoset`: **Shimura, Proposition 3.31** — `toLevelOneCoset` is
  injective on the set of coprime-determinant double cosets.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Propositions 3.30 and 3.31.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- An element of `Δ₀(N)` has **coprime determinant** when every integral matrix representing
it has determinant coprime to `N`.

Quantifying over all representatives rather than choosing one keeps the predicate free of a
choice; the representative is unique anyway, since `ℤ → ℚ` is injective. -/
def CoprimeDet (g : Delta0 N) : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) →
      Int.gcd A.det N = 1

/-- **Shimura, Proposition 3.30.** Passing from a `Γ₀(N)`-double coset to the level-one double
coset of the same element, as the `HeckeCoset.map` of the three inclusions `Δ₀(N) ≤ Δ`,
`Γ₀(N) ≤ SL₂(ℤ)` (twice). -/
noncomputable def toLevelOneCoset :
    HeckeCoset (Delta0 N) (Gamma0Image N) (Gamma0Image N) →
      HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2) :=
  HeckeCoset.map (Delta0_le_posDetInt N) (Gamma0Image_le_SLnZ N) (Gamma0Image_le_SLnZ N)

/-- The computation rule for `toLevelOneCoset`: it keeps the representative and forgets the
level. -/
@[simp] lemma toLevelOneCoset_mk (g : Delta0 N) :
    toLevelOneCoset N (HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) g) =
      HeckeCoset.mk (SLnZ 2) (SLnZ 2) (Submonoid.inclusion (Delta0_le_posDetInt N) g) :=
  HeckeCoset.map_mk _ _ _ g

/-- An `SL₂(ℤ)`-coefficient has determinant one, so multiplying by it does not change the
determinant of the integral matrix. -/
private lemma intMatrix_det_eq_of_mem_doubleCoset {a b : GL (Fin 2) ℚ}
    (hb : b ∈ DoubleCoset.doubleCoset a (Gamma0Image N) (Gamma0Image N))
    {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (↑a : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hB : (↑b : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ)) : B.det = A.det := by
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hb
  obtain ⟨σ₁, rfl⟩ := (mem_SLnZ_iff 2).mp (Gamma0Image_le_SLnZ N hγ₁)
  obtain ⟨σ₂, rfl⟩ := (mem_SLnZ_iff 2).mp (Gamma0Image_le_SLnZ N hγ₂)
  -- over `ℚ` the two determinants agree, and `ℤ → ℚ` is injective
  have hcast : ((B.det : ℤ) : ℚ) = ((A.det : ℤ) : ℚ) := by
    have hB' : ((B.det : ℤ) : ℚ) = (↑(mapGL ℚ σ₁ * a * mapGL ℚ σ₂) :
        Matrix (Fin 2) (Fin 2) ℚ).det := by
      rw [hB]; simpa [RingHom.mapMatrix_apply] using RingHom.map_det (Int.castRingHom ℚ) B
    have hA' : ((A.det : ℤ) : ℚ) = (↑a : Matrix (Fin 2) (Fin 2) ℚ).det := by
      rw [hA]; simpa [RingHom.mapMatrix_apply] using RingHom.map_det (Int.castRingHom ℚ) A
    -- `det_mapGL` is about the *unit* determinant, so `← val_det_apply` moves the matrix
    -- determinant of an `SL₂(ℤ)` coefficient into its range first
    rw [hB', hA', GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, Matrix.det_mul,
      Matrix.det_mul]
    simp only [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one, one_mul, mul_one]
  exact_mod_cast hcast

/-- Coprimality of the determinant to the level depends only on the double coset. -/
private lemma coprimeDet_congr {a b : Delta0 N}
    (h : HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) a =
      HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) b) :
    CoprimeDet N a ↔ CoprimeDet N b := by
  obtain ⟨Aa, hAa, -, -, -⟩ := (mem_Delta0_iff N).mp a.2
  obtain ⟨Ab, hAb, -, -, -⟩ := (mem_Delta0_iff N).mp b.2
  have hdc := HeckeCoset.eq_iff.mp h
  have hba : Ab.det = Aa.det := intMatrix_det_eq_of_mem_doubleCoset N
    (hdc ▸ DoubleCoset.mem_doubleCoset_self _ _ _) hAa hAb
  constructor
  · intro ha A hA
    obtain rfl : A = Ab := Matrix.map_injective Int.cast_injective (hA.symm.trans hAb)
    exact hba ▸ ha Aa hAa
  · intro hb A hA
    obtain rfl : A = Aa := Matrix.map_injective Int.cast_injective (hA.symm.trans hAa)
    exact hba ▸ hb Ab hAb

/-- Coprimality of the determinant to the level, as a predicate on `Γ₀(N)`-double cosets. -/
def CoprimeDetCoset : HeckeCoset (Delta0 N) (Gamma0Image N) (Gamma0Image N) → Prop :=
  Quotient.lift (CoprimeDet N)
    (fun _ _ hab ↦ propext (coprimeDet_congr N (Quotient.sound hab)))

/-- `CoprimeDetCoset` is `CoprimeDet` on any representative. -/
@[simp] lemma coprimeDetCoset_mk (g : Delta0 N) :
    CoprimeDetCoset N (HeckeCoset.mk (Gamma0Image N) (Gamma0Image N) g) ↔ CoprimeDet N g :=
  Iff.rfl

/-- **Shimura, Proposition 3.31.** `toLevelOneCoset` is injective on the double cosets whose
determinant is coprime to `N`: the level-one double coset determines the `Γ₀(N)` one, because
intersecting it with `Δ₀(N)` returns the latter. -/
theorem injOn_toLevelOneCoset :
    Set.InjOn (toLevelOneCoset N) {D | CoprimeDetCoset N D} := by
  rintro D₁ hD₁ D₂ hD₂ h
  -- work with representatives, so that `toLevelOneCoset_mk` applies
  have hD₁' : CoprimeDet N D₁.rep :=
    (coprimeDetCoset_mk N D₁.rep).mp (by rwa [HeckeCoset.mk_rep])
  have hD₂' : CoprimeDet N D₂.rep :=
    (coprimeDetCoset_mk N D₂.rep).mp (by rwa [HeckeCoset.mk_rep])
  rw [← HeckeCoset.mk_rep D₁, ← HeckeCoset.mk_rep D₂] at h ⊢
  rw [toLevelOneCoset_mk, toLevelOneCoset_mk, HeckeCoset.eq_iff, Submonoid.coe_inclusion,
    Submonoid.coe_inclusion] at h
  obtain ⟨Aa, hAa, -, -, -⟩ := (mem_Delta0_iff N).mp D₁.rep.2
  obtain ⟨Ab, hAb, -, -, -⟩ := (mem_Delta0_iff N).mp D₂.rep.2
  refine HeckeCoset.eq_iff.mpr ?_
  -- each `Γ₀(N)`-double coset is its level-one one cut down to `Δ₀(N)`, and those agree
  rw [← doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image N _ D₁.rep.2 Aa hAa
      (hD₁' Aa hAa),
    ← doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image N _ D₂.rep.2 Ab hAb
      (hD₂' Ab hAb), h]

end HeckeRing.GL2
