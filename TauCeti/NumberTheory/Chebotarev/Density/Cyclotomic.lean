/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
import TauCeti.Analysis.SpecialFunctions.Log.OneDivSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.PrimeSum
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum
import TauCeti.NumberTheory.Chebotarev.Density.Ramification
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Orthogonality
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Series

/-!
# Chebotarev density for cyclotomic extensions

Let `F = K(μ_m)` be a cyclotomic extension of the number field `K`. For every `σ ∈ Gal(F/K)`,
the primes of `𝓞 K` whose Frobenius is `σ` have Dirichlet density `1 / #Gal(F/K)`.

## Main results

* `NumberField.Chebotarev.hasDirichletDensity_cyclotomicFrobenius`: the Frobenius fibre of any
  `σ ∈ Gal(K(μ_m)/K)` has Dirichlet density `1 / #Gal(K(μ_m)/K)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* The same character-orthogonality argument is formalized as `Chebotarev.chebotarev_cyclotomic`
  in AINTLIB, <https://github.com/CBirkbeck/aintlib> (Apache-2.0), commit
  `8102fa09bbf570f3e991adfdb2d6d70b48cb5b5e`, file
  `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean`.
-/

open Filter IsDedekindDomain NumberField TauCeti
open scoped NumberField nonZeroDivisors Topology

namespace NumberField.Chebotarev

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

open scoped Classical IsMulCommutative in
-- Character orthogonality at every prime, the ramified ones included: the character sum is
-- `#Gal(F/K)` on the Frobenius fibre of `σ` and `0` off it.
private theorem sum_inv_mul_galoisCharacterWeight_eq_ite [IsMulCommutative (F ≃ₐ[K] F)]
    (σ : F ≃ₐ[K] F) (P : HeightOneSpectrum (𝓞 K)) :
    ∑ χ : (F ≃ₐ[K] F) →* ℂˣ,
        (((χ σ)⁻¹ : ℂˣ) : ℂ) * MonoidHom.galoisCharacterWeight (L := F) χ P.asIdeal =
      if P ∈ frobeniusPrimeSet K F (ConjClasses.mk σ) then (Nat.card (F ≃ₐ[K] F) : ℂ) else 0 := by
  by_cases hP : P ∈ ramifiedPrimes K F
  · rw [AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_eq_zero_of_mem_ramifiedPrimes σ P hP,
      ite_eq_right fun h ↦ frobeniusPrimeSet_subset_compl_ramifiedPrimes _ h hP]
  · rw [mem_ramifiedPrimes_iff, not_not] at hP
    rw [AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_of_unramified σ P hP,
      mem_frobeniusPrimeSet_iff_artinSymbol_eq hP]
    generalize artinSymbol P.asIdeal hP = c
    -- In an abelian group a conjugacy class is the class of its representative alone.
    congr 1
    have hc : ConjClasses.mk c.out = c := Quotient.out_eq c
    rw [← ConjClasses.mk_injective.eq_iff (a := c.out), hc]

-- The weight of a Galois character is bounded by `1`.
private theorem norm_galoisCharacterWeight_le_one (χ : (F ≃ₐ[K] F) →* ℂˣ) (I : Ideal (𝓞 K)) :
    ‖MonoidHom.galoisCharacterWeight (L := F) χ I‖ ≤ 1 := by
  simpa using χ.galoisCharacterUnitaryWeight.norm_le_one I

-- The prime sum of the trivial character is the prime sum over the unramified primes.
private theorem primeSum_galoisCharacterWeight_one (t : ℝ) :
    (MonoidHom.galoisCharacterWeight (L := F) (1 : (F ≃ₐ[K] F) →* ℂˣ)).primeSum t =
      ((↑(ramifiedPrimes K F) : Set (HeightOneSpectrum (𝓞 K)))ᶜ.primeIdealZetaSum t : ℂ) := by
  classical
  simp [Set.ofReal_primeIdealZetaSum, MultiplicativeIdealWeight.primeSum_def,
    Ideal.isPrimeTo_asIdeal_iff]

-- **The Frobenius fibre by orthogonality.** For `F / K` abelian and `t > 1`, `#Gal(F/K)` times
-- the prime sum over the Frobenius fibre of `σ` is `∑ χ, χ(σ)⁻¹ P_χ(t)`.
private theorem natCard_mul_primeIdealZetaSum_eq [IsMulCommutative (F ≃ₐ[K] F)] (σ : F ≃ₐ[K] F)
    {t : ℝ} (ht : 1 < t) :
    (Nat.card (F ≃ₐ[K] F) : ℂ) *
        ((frobeniusPrimeSet K F (ConjClasses.mk σ)).primeIdealZetaSum t : ℂ) =
      ∑ χ : (F ≃ₐ[K] F) →* ℂˣ,
        (((χ σ)⁻¹ : ℂˣ) : ℂ) * (MonoidHom.galoisCharacterWeight (L := F) χ).primeSum t := by
  simp only [MultiplicativeIdealWeight.primeSum_def, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun χ _ ↦
      ((MonoidHom.galoisCharacterWeight χ).summable_div_of_summable_idealTerm
        (summable_idealTerm_of_bounded_of_one_lt_re
          (MultiplicativeIdealWeight.norm_toIdealArithmeticFunction_le_one
            (norm_galoisCharacterWeight_le_one K F χ))
          (by simpa using ht))).mul_left _,
    Set.ofReal_primeIdealZetaSum, ← tsum_mul_left]
  refine tsum_congr fun P ↦ ?_
  simp only [mul_div_assoc', ← Finset.sum_div, sum_inv_mul_galoisCharacterWeight_eq_ite]
  simp

open scoped Classical in
-- The normalized prime sum of a character tends to `1` for the trivial character, whose primes are
-- the unramified ones, and to `0` for the others, whose prime sums stay bounded.
private theorem tendsto_primeSum_galoisCharacterWeight_div_log (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) :
    Tendsto (fun t : ℝ ↦ (MonoidHom.galoisCharacterWeight (L := F) χ).primeSum t /
      (Real.log (1 / (t - 1)) : ℂ)) (𝓝[>] 1) (𝓝 (if χ = 1 then 1 else 0)) := by
  split_ifs with hχ
  · subst hχ
    refine ((Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one _ _).mp
      (hasDirichletDensity_compl_ramifiedPrimes K F)).ofReal.congr fun t ↦ ?_
    rw [primeSum_galoisCharacterWeight_one, Complex.ofReal_div]
  · have hℓ := Real.tendsto_log_one_div_sub_atTop 1
    obtain ⟨B, hB⟩ := MultiplicativeIdealWeight.exists_norm_primeSum_le
      (norm_galoisCharacterWeight_le_one K F χ)
      (cyclotomicCharacterSeriesC_analyticAt_one K F m χ hχ)
      (cyclotomicCharacterSeriesC_ne_zero_at_one K F m χ hχ)
      fun _ ↦ cyclotomicCharacterSeriesC_eq_LSeries K F χ
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := B)).div_atTop hℓ)
    filter_upwards [hB, hℓ.eventually_gt_atTop 0] with t hBt hℓt
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hℓt.le]
    gcongr

end NumberField.Chebotarev

public section

namespace NumberField.Chebotarev

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

/-- **Chebotarev density for cyclotomic extensions.** For `F = K(μ_m)` and any `σ ∈ Gal(F/K)`,
the primes of `𝓞 K` whose Frobenius in `F` is `σ` have Dirichlet density `1 / #Gal(F/K)`. -/
theorem hasDirichletDensity_cyclotomicFrobenius (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (σ : F ≃ₐ[K] F) :
    NumberField.Set.HasDirichletDensity (frobeniusPrimeSet K F (ConjClasses.mk σ))
      (1 / (Nat.card (F ≃ₐ[K] F) : ℝ)) := by
  classical
  have := IsCyclotomicExtension.isMulCommutative {m} K F
  rw [Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one, ← tendsto_ofReal_iff]
  -- Summed against `(χ σ)⁻¹`, only the trivial character's normalized prime sum survives.
  convert ((tendsto_finsetSum Finset.univ fun χ _ ↦
    (tendsto_primeSum_galoisCharacterWeight_div_log K F m χ).const_mul
      (((χ σ)⁻¹ : ℂˣ) : ℂ)).const_mul (1 / (Nat.card (F ≃ₐ[K] F) : ℂ))).congr' ?_ using 2
  · simp
  filter_upwards [self_mem_nhdsWithin] with t (ht : 1 < t)
  simp only [mul_div_assoc', ← Finset.sum_div, ← natCard_mul_primeIdealZetaSum_eq K F σ ht]
  simp

end NumberField.Chebotarev
