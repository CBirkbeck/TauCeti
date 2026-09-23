/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.PartialSums

/-!
# Cancellation for the ideal weight of a cyclotomic Galois character

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K` and `χ` a character of
`Gal(F/K)`. On the integral ideals prime to `m`, the ideal weight `galoisCharacterWeight χ` is the
ray class character `χ ∘ cyclotomicArtin K F m` of `cyclotomicModulus K m`. So once the Euler
factors at the primes dividing `m` are deleted, the ideal partial sums of the weight are the
partial sums of that ray class character, and when the ray class character is nontrivial they are
`O(x ^ (1 - 1 / [K : ℚ]))`.

The deletion is needed for the identification: a prime dividing `m` may be unramified in `F`, and
there the weight is a root of unity rather than `0`. In degree `[K : ℚ] > 1` the cancellation
exponent is positive and the deleted Euler factors can be restored
(`TauCeti.hasCancellation_restrict_iff`).

## Main results

* `MonoidHom.hasCancellation_restrict_galoisCharacterUnitaryWeight`: the weight restricted away
  from the primes dividing `m` has cancellation.
* `MonoidHom.hasCancellation_galoisCharacterUnitaryWeight`: in degree `[K : ℚ] > 1`, the weight
  itself has cancellation.
-/

public section

open Asymptotics Filter IsDedekindDomain NumberField TauCeti TauCeti.GlobalNumberFields
open scoped nonZeroDivisors NumberField

namespace MonoidHom

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F]
  [Algebra K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

/-- The ideal partial sums of the Galois weight with the Euler factors at the primes dividing `m`
deleted are the partial sums of the ray class character `χ ∘ cyclotomicArtin K F m`. -/
private theorem idealSummatory_restrict_galoisCharacterUnitaryWeight (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (x : ℝ) :
    idealSummatory K ((galoisCharacterUnitaryWeight (L := F) χ).restrict
        ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K)))
        (cyclotomicModulus K m).support.finite_toSet).toIdealArithmeticFunction x =
      rayClassCharacterPartialSum (cyclotomicModulus K m) (χ.comp (cyclotomicArtin K F m)) x := by
  classical
  set 𝔪 := cyclotomicModulus K m
  have hmem (J : Ideal (𝓞 K)) :
      J ∈ integralIdealsPrimeTo 𝔪 ↔ J.IsPrimeTo (𝔪.support : Set (HeightOneSpectrum (𝓞 K))) :=
    NumberFieldArithmetic.mem_integralIdealsAway_iff.trans Ideal.isPrimeTo_iff.symm
  let e : integralIdealsPrimeTo 𝔪 → (Ideal (𝓞 K))⁰ := fun I ↦
    ⟨I, mem_nonZeroDivisors_of_ne_zero ((hmem I).mp I.2).ne_bot⟩
  have hsum : rayClassCharacterPartialSum 𝔪 (χ.comp (cyclotomicArtin K F m)) x =
      ∑ I ∈ normLE (fun I : integralIdealsPrimeTo 𝔪 ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x,
        (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ) := by
    rw [rayClassCharacterPartialSum_def, ← finsum_mem_coe_finset, coe_normLE]
    exact finsum_set_coe_eq_finsum_mem
      (f := fun I ↦ (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ)) _
  rw [hsum, idealSummatory_apply]
  refine (Finset.sum_of_injOn e (fun I _ J _ h ↦ Subtype.ext (by simpa [e] using h))
    (fun I hI ↦ by simpa [e] using hI) (fun J hJ hJe ↦ ?_) (fun I _ ↦ ?_)).symm
  · rw [UnitaryIdealWeight.toIdealArithmeticFunction_apply, UnitaryIdealWeight.val_restrict,
      MultiplicativeIdealWeight.restrict_apply, ite_eq_right_iff]
    intro hJ𝔪
    exact absurd ⟨⟨J, (hmem J).mpr hJ𝔪⟩, by simpa using hJ, rfl⟩ hJe
  · have hI : (I : Ideal (𝓞 K)).IsPrimeTo
        ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K))) := (hmem I).mp I.2
    simp only [UnitaryIdealWeight.toIdealArithmeticFunction_apply,
      UnitaryIdealWeight.val_restrict, MultiplicativeIdealWeight.restrict_apply, e, hI,
      ↓reduceIte, val_galoisCharacterUnitaryWeight]
    exact (galoisCharacterWeight_eq_onIdeals χ I).symm

/-- **Cancellation for a cyclotomic Galois character, away from the level.** For `F = K(μ_m)`
and a character `χ` of `Gal(F/K)` whose ray class character `χ ∘ cyclotomicArtin K F m` is
nontrivial, the ideal weight of `χ` with the Euler factors at the primes dividing `m` deleted has
cancellation. -/
theorem hasCancellation_restrict_galoisCharacterUnitaryWeight (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ.comp (cyclotomicArtin K F m) ≠ 1) :
    HasCancellation ((galoisCharacterUnitaryWeight (L := F) χ).restrict
      ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K)))
      (cyclotomicModulus K m).support.finite_toSet) := by
  rw [hasCancellation_iff_isBigO, one_div]
  simp_rw [idealSummatory_restrict_galoisCharacterUnitaryWeight]
  exact isBigO_rayClassCharacterPartialSum _ _ hχ

/-- **Cancellation for a cyclotomic Galois character.** For `F = K(μ_m)` over a number field `K`
of degree `[K : ℚ] > 1`, and a character `χ` of `Gal(F/K)` whose ray class character
`χ ∘ cyclotomicArtin K F m` is nontrivial, the ideal partial sums of the weight of `χ` are
`O(x ^ (1 - 1 / [K : ℚ]))`. -/
theorem hasCancellation_galoisCharacterUnitaryWeight (hK : 1 < Module.finrank ℚ K)
    (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ.comp (cyclotomicArtin K F m) ≠ 1) :
    HasCancellation (galoisCharacterUnitaryWeight (L := F) χ) :=
  (hasCancellation_restrict_iff _ _ hK).mp
    (hasCancellation_restrict_galoisCharacterUnitaryWeight χ hχ)

end MonoidHom
