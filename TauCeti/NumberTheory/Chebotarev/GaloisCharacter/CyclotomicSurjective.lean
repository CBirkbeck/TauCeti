/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic
import TauCeti.NumberTheory.Chebotarev.Density.SplitsCompletely

/-!
# Surjectivity of the cyclotomic Artin map

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K`. The Artin map
`cyclotomicArtin K F m` from the ray class group of `cyclotomicModulus K m` to `Gal(F/K)` is
surjective.

## Main results

* `TauCeti.GlobalNumberFields.cyclotomicArtin_surjective`: the cyclotomic Artin map is
  surjective.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §7 and Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter VIII, §4.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField IntermediateField
open scoped NumberField symmDiff

namespace TauCeti.GlobalNumberFields

open NumberFieldArithmetic NumberField.Chebotarev

variable (K : Type*) [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F]
  [Algebra K F] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

/-- **The cyclotomic Artin map is surjective.** For `F = K(μ_m)`, every automorphism of `F / K` is
the Artin automorphism of a ray class of `cyclotomicModulus K m`. -/
theorem cyclotomicArtin_surjective : Function.Surjective (cyclotomicArtin K F m) := by
  have := IsCyclotomicExtension.isMulCommutative {m} K F
  set H := (cyclotomicArtin K F m).range
  -- Every prime not dividing `m` has its Frobenius in the image `H`, so it splits completely in
  -- the fixed field of `H`.
  have hsplit (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
      𝔭 ∈ frobeniusPrimeSet K (fixedField H) 1 := by
    have hmem : 𝔭.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m) :=
      asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mpr h𝔭
    -- The weight of the trivial character is a unit at `𝔭`, so `𝔭` is unramified in `F`.
    have hram : 𝔭 ∉ ramifiedPrimes K F := by
      rw [← MonoidHom.galoisCharacterWeight_apply_eq_zero_iff (1 : (F ≃ₐ[K] F) →* ℂˣ)]
      have h := MonoidHom.galoisCharacterWeight_eq_onIdeals (m := m) (F := F) 1 ⟨_, hmem⟩
      exact h ▸ Units.ne_zero _
    rw [mem_ramifiedPrimes_iff, not_not] at hram
    obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 F)))
    obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)
    have hσH : AlgEquiv.restrictNormalHom (fixedField H) σ = 1 := by
      rw [← MonoidHom.mem_ker, restrictNormalHom_ker, fixingSubgroup_fixedField]
      exact ⟨_, cyclotomicArtin_idealClass_of_isArithFrobAt F m 𝔭 hmem Q hσ⟩
    have hmk : ConjClasses.map (AlgEquiv.restrictNormalHom (fixedField H)) (.mk σ) = 1 := by
      change ConjClasses.mk _ = _
      rw [hσH, ConjClasses.one_eq_mk_one]
    exact hmk ▸ frobeniusPrimeSet_subset_map_restrictNormalHom (M := fixedField H) _
      (mem_frobeniusPrimeSet_mk_of_isArithFrobAt hram Q hσ)
  -- So the completely split primes of the fixed field have density one; they also have density
  -- `1 / [E : K]`, so the fixed field is `K` and `H` is the whole Galois group.
  have hfin : (frobeniusPrimeSet K (fixedField H) 1 ∆ Set.univ).Finite := by
    refine (cyclotomicModulus K m).support.finite_toSet.subset fun 𝔭 h𝔭 ↦ ?_
    rw [Finset.mem_coe, mem_cyclotomicModulus_support_iff]
    by_contra h
    simp [Set.mem_symmDiff, hsplit 𝔭 h] at h𝔭
  have hdeg := (hasDirichletDensity_frobeniusPrimeSet_one K (fixedField H)).unique
    (Set.hasDirichletDensity_univ.of_finite_symmDiff hfin)
  rw [one_div, inv_eq_one, Nat.cast_eq_one, IntermediateField.finrank_eq_one_iff] at hdeg
  rw [← MonoidHom.range_eq_top, ← fixingSubgroup_fixedField (cyclotomicArtin K F m).range, hdeg,
    fixingSubgroup_bot]

end TauCeti.GlobalNumberFields
