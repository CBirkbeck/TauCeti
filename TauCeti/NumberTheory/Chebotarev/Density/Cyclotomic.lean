/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
import Mathlib.NumberTheory.EulerProduct.ExpLog
import TauCeti.Analysis.SpecialFunctions.Log.OneDivSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Deriv
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
-/

open Filter IsDedekindDomain NumberField TauCeti
open scoped NumberField nonZeroDivisors Topology

namespace NumberField.Chebotarev

section PrimeSum

variable {K : Type*} [Field K] [NumberField K]

-- The prime-indexed Dirichlet series `∑_𝔭 w(𝔭) N(𝔭)⁻ᵗ` of an ideal weight at a real point.
private noncomputable def primeSum (w : MultiplicativeIdealWeight K) (t : ℝ) : ℂ :=
  ∑' P : HeightOneSpectrum (𝓞 K), w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (t : ℂ)

-- The prime-power expansion `∑_{𝔭, e} (w(𝔭) N(𝔭)⁻ᶻ) ^ (e + 1) / (e + 1)` of a logarithm of the
-- `L`-series of an ideal weight.
private noncomputable def powerSum (w : MultiplicativeIdealWeight K) (z : ℂ) : ℂ :=
  ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
    (w pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1)

variable {w : MultiplicativeIdealWeight K}

-- A weight bounded by `1` gives an ideal arithmetic function bounded by `1`.
private theorem norm_toIdealArithmeticFunction_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1)
    (I : (Ideal (𝓞 K))⁰) : ‖w.toIdealArithmeticFunction I‖ ≤ 1 := by
  simpa using hw I

-- For `t ≥ 1` the local ratio `w(𝔭) N(𝔭)⁻ᵗ` of a weight bounded by `1` is at most `N(𝔭)⁻¹`.
private theorem norm_div_absNorm_cpow_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1)
    (P : HeightOneSpectrum (𝓞 K)) {t : ℝ} (ht : 1 ≤ t) :
    ‖w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (t : ℂ)‖ ≤ (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
  have hN : (1 : ℝ) ≤ Ideal.absNorm P.asIdeal := one_le_two.trans (two_le_absNorm_asIdeal_real P)
  rw [norm_div, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast zero_lt_one.trans_le hN),
    Complex.ofReal_re]
  calc ‖w P.asIdeal‖ / (Ideal.absNorm P.asIdeal : ℝ) ^ t
      ≤ 1 / (Ideal.absNorm P.asIdeal : ℝ) ^ (1 : ℝ) := by
        gcongr
        exact hw _
    _ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by rw [Real.rpow_one, one_div]

-- For `‖z‖ ≤ 1 / 2`, the Euler-factor logarithm `-log (1 - z)` differs from `z` by at most
-- `‖z‖ ^ 2`.
private theorem norm_neg_log_one_sub_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
  have h := Complex.norm_log_one_add_sub_self_le (z := -z)
    (by simpa using hz.trans_lt one_half_lt_one)
  rw [norm_neg, ← sub_eq_add_neg, ← norm_neg, sub_neg_eq_add, neg_add] at h
  have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  calc ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
        rwa [sub_eq_add_neg]
    _ ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖z‖ ^ 2 := by ring

-- **The prime-power tail is bounded.** For a weight bounded by `1` and real `t > 1`, the
-- prime-power expansion differs from the prime sum by at most `2 [K : ℚ]`.
private theorem norm_powerSum_sub_primeSum_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {t : ℝ}
    (ht : 1 < t) : ‖powerSum w t - primeSum w t‖ ≤ 2 * Module.finrank ℚ K := by
  have hs := summable_idealTerm_of_bounded_of_one_lt_re (norm_toIdealArithmeticFunction_le hw)
    (s := t) (by simpa using ht)
  have hr := w.summable_div_of_summable_idealTerm hs
  -- Regroup the prime-power expansion prime by prime into Euler-factor logarithms.
  rw [powerSum, w.tsum_prime_pow_eq_tsum_neg_log_one_sub hs, primeSum,
    ← hr.clog_one_sub.neg.tsum_sub hr]
  refine (tsum_of_norm_bounded (summable_absNorm_rpow_primes_of_one_lt one_lt_two).hasSum
    fun P ↦ ?_).trans tsum_absNorm_rpow_neg_two_le
  have hx := norm_div_absNorm_cpow_le hw P ht.le
  refine (norm_neg_log_one_sub_sub_le (hx.trans ?_)).trans ?_
  · rw [one_div]
    exact inv_anti₀ two_pos (two_le_absNorm_asIdeal_real P)
  · rw [Real.rpow_neg (by positivity), Real.rpow_two, ← inv_pow]
    gcongr

-- A function whose derivative along `(a, ∞)` extends continuously to `a` stays bounded near `a⁺`.
private theorem exists_norm_le_of_hasDerivAt_of_continuousAt {f g : ℂ → ℂ} {a : ℝ}
    (hg : ContinuousAt g a) (hf : ∀ u : ℝ, a < u → HasDerivAt f (g u) u) :
    ∃ B, ∀ᶠ t : ℝ in 𝓝[>] a, ‖f t‖ ≤ B := by
  -- `‖g‖ < ‖g a‖ + 1` near `a`, so `f` is Lipschitz along the reals there.
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hg.comp Complex.continuous_ofReal.continuousAt).norm.eventually_lt continuousAt_const
      (lt_add_one ‖g a‖))
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ ∈ Set.Ioo a (a + ε) := ⟨a + ε / 2, by linarith, by linarith⟩
  refine ⟨‖f x₀‖ + (‖g a‖ + 1) * ε, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show a < a + ε by linarith)] with t ht
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ ↦ f u) (f' := fun u : ℝ ↦ g u)
    (fun u hu ↦ ((hf u hu.1).comp_ofReal).hasDerivWithinAt)
    (fun u hu ↦ (hball (by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2])).le) (convex_Ioo _ _) hx₀ ht
  have hdist : ‖t - x₀‖ ≤ ε := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2, hx₀.1, hx₀.2]
  calc ‖f t‖ ≤ ‖f x₀‖ + ‖f t - f x₀‖ := norm_le_insert' _ _
    _ ≤ ‖f x₀‖ + (‖g a‖ + 1) * ε := by
        gcongr
        exact hmvt.trans (by gcongr)

-- On `Re z > 1`, the prime-power expansion is a primitive of the logarithmic derivative of any
-- function agreeing there with the `L`-series.
private theorem hasDerivAt_powerSum (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {C : ℂ → ℂ}
    (hCL : ∀ z : ℂ, 1 < z.re → C z = LSeries (normCoeff K w.toIdealArithmeticFunction) z) {z : ℂ}
    (hz : 1 < z.re) : HasDerivAt (powerSum w) (logDeriv C z) z := by
  have habs := idealAbscissaOfAbsConv_lt_re_of_bounded (norm_toIdealArithmeticFunction_le hw) hz
  have heq : C =ᶠ[𝓝 z] LSeries (normCoeff K w.toIdealArithmeticFunction) :=
    eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz) hCL
  rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds, ← logDeriv_apply,
    w.logDeriv_LSeries_eq_tsum_prime_pow habs]
  exact w.hasDerivAt_tsum_prime_pow habs

-- **A logarithm of a continued `L`-series stays bounded.** If the `L`-series of a weight
-- bounded by `1` agrees on `Re s > 1` with a function analytic and nonzero at `s = 1`, then its
-- prime-power expansion is bounded as `t → 1⁺`.
private theorem exists_norm_powerSum_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {C : ℂ → ℂ}
    (hC : AnalyticAt ℂ C 1) (hC1 : C 1 ≠ 0)
    (hCL : ∀ z : ℂ, 1 < z.re → C z = LSeries (normCoeff K w.toIdealArithmeticFunction) z) :
    ∃ B, ∀ᶠ t : ℝ in 𝓝[>] 1, ‖powerSum w t‖ ≤ B := by
  refine exists_norm_le_of_hasDerivAt_of_continuousAt ?_
    fun u hu ↦ hasDerivAt_powerSum hw hCL (by simpa using hu)
  exact hC.deriv.continuousAt.div hC.continuousAt hC1

-- **The prime sum of a continued `L`-series stays bounded.**
private theorem exists_norm_primeSum_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {C : ℂ → ℂ}
    (hC : AnalyticAt ℂ C 1) (hC1 : C 1 ≠ 0)
    (hCL : ∀ z : ℂ, 1 < z.re → C z = LSeries (normCoeff K w.toIdealArithmeticFunction) z) :
    ∃ B, ∀ᶠ t : ℝ in 𝓝[>] 1, ‖primeSum w t‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_norm_powerSum_le hw hC hC1 hCL
  refine ⟨B + 2 * Module.finrank ℚ K, ?_⟩
  filter_upwards [hB, self_mem_nhdsWithin] with t hBt (ht : 1 < t)
  calc ‖primeSum w t‖ ≤ ‖powerSum w t‖ + ‖powerSum w t - primeSum w t‖ := norm_le_insert _ _
    _ ≤ _ := add_le_add hBt (norm_powerSum_sub_primeSum_le hw ht)

open scoped Classical in
-- The prime-ideal zeta sum of a set of primes, as a complex prime sum of its indicator.
private theorem ofReal_primeIdealZetaSum (S : Set (HeightOneSpectrum (𝓞 K))) (t : ℝ) :
    (S.primeIdealZetaSum t : ℂ) = ∑' P : HeightOneSpectrum (𝓞 K),
      (if P ∈ S then 1 else 0) / (Ideal.absNorm P.asIdeal : ℂ) ^ (t : ℂ) := by
  rw [Set.primeIdealZetaSum_def,
    tsum_subtype S fun P ↦ (Ideal.absNorm P.asIdeal : ℝ) ^ (-t), Complex.ofReal_tsum]
  refine tsum_congr fun P ↦ ?_
  by_cases h : P ∈ S <;>
    simp [h, Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_cpow (Nat.cast_nonneg _)]

end PrimeSum

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
    rw [← ConjClasses.mk_injective.eq_iff (a := c.out),
      show ConjClasses.mk c.out = c from Quotient.out_eq c]

-- The weight of a Galois character is bounded by `1`.
private theorem norm_galoisCharacterWeight_le_one (χ : (F ≃ₐ[K] F) →* ℂˣ) (I : Ideal (𝓞 K)) :
    ‖MonoidHom.galoisCharacterWeight (L := F) χ I‖ ≤ 1 := by
  simpa using χ.galoisCharacterUnitaryWeight.norm_le_one I

-- The prime sum of the trivial character is the prime sum over the unramified primes.
private theorem primeSum_galoisCharacterWeight_one (t : ℝ) :
    primeSum (MonoidHom.galoisCharacterWeight (L := F) (1 : (F ≃ₐ[K] F) →* ℂˣ)) t =
      ((↑(ramifiedPrimes K F) : Set (HeightOneSpectrum (𝓞 K)))ᶜ.primeIdealZetaSum t : ℂ) := by
  classical
  simp [ofReal_primeIdealZetaSum, primeSum, Ideal.isPrimeTo_asIdeal_iff]

-- **The Frobenius fibre by orthogonality.** For `F / K` abelian and `t > 1`, `#Gal(F/K)` times
-- the prime sum over the Frobenius fibre of `σ` is `∑ χ, χ(σ)⁻¹ P_χ(t)`.
private theorem natCard_mul_primeIdealZetaSum_eq [IsMulCommutative (F ≃ₐ[K] F)] (σ : F ≃ₐ[K] F)
    {t : ℝ} (ht : 1 < t) :
    (Nat.card (F ≃ₐ[K] F) : ℂ) *
        ((frobeniusPrimeSet K F (ConjClasses.mk σ)).primeIdealZetaSum t : ℂ) =
      ∑ χ : (F ≃ₐ[K] F) →* ℂˣ,
        (((χ σ)⁻¹ : ℂˣ) : ℂ) * primeSum (MonoidHom.galoisCharacterWeight (L := F) χ) t := by
  simp only [primeSum, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun χ _ ↦
      ((MonoidHom.galoisCharacterWeight χ).summable_div_of_summable_idealTerm
        (summable_idealTerm_of_bounded_of_one_lt_re
          (norm_toIdealArithmeticFunction_le (norm_galoisCharacterWeight_le_one K F χ))
          (by simpa using ht))).mul_left _,
    ofReal_primeIdealZetaSum, ← tsum_mul_left]
  refine tsum_congr fun P ↦ ?_
  simp only [mul_div_assoc', ← Finset.sum_div, sum_inv_mul_galoisCharacterWeight_eq_ite]
  simp

open scoped Classical in
-- The normalized prime sum of a character tends to `1` for the trivial character, whose primes are
-- the unramified ones, and to `0` for the others, whose prime sums stay bounded.
private theorem tendsto_primeSum_galoisCharacterWeight_div_log (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) :
    Tendsto (fun t : ℝ ↦ primeSum (MonoidHom.galoisCharacterWeight (L := F) χ) t /
      (Real.log (1 / (t - 1)) : ℂ)) (𝓝[>] 1) (𝓝 (if χ = 1 then 1 else 0)) := by
  split_ifs with hχ
  · subst hχ
    refine ((Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one _ _).mp
      (hasDirichletDensity_compl_ramifiedPrimes K F)).ofReal.congr fun t ↦ ?_
    rw [primeSum_galoisCharacterWeight_one, Complex.ofReal_div]
  · have hℓ := Real.tendsto_log_one_div_sub_atTop 1
    obtain ⟨B, hB⟩ := exists_norm_primeSum_le (norm_galoisCharacterWeight_le_one K F χ)
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
