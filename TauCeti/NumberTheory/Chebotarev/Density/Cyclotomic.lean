/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
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

## Implementation notes

Character orthogonality writes `#Gal(F/K)` times the prime sum over the fibre of `σ` as
`∑ χ, χ(σ)⁻¹ P_χ(s)`, where `P_χ(s) = ∑_𝔭 χ(Frob 𝔭) N(𝔭)⁻ˢ`. The trivial character contributes
the sum over the unramified primes. For a nontrivial `χ`, `P_χ(s)` stays bounded as `s → 1⁺`: it
differs by a bounded prime-power tail from a logarithm of the `L`-series of `χ`, whose derivative,
the logarithmic derivative of `cyclotomicCharacterSeriesC K F χ`, is bounded near `s = 1` because
that series is analytic and nonzero there.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

open Filter IsDedekindDomain NumberField TauCeti
open scoped NumberField nonZeroDivisors Topology

namespace NumberField.Chebotarev

section PrimeSum

variable {K : Type*} [Field K] [NumberField K]

/-- The prime-indexed Dirichlet series `∑_𝔭 w(𝔭) N(𝔭)⁻ᵗ` of an ideal weight at a real point. -/
private noncomputable def primeSum (w : MultiplicativeIdealWeight K) (t : ℝ) : ℂ :=
  ∑' P : HeightOneSpectrum (𝓞 K), w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (t : ℂ)

/-- The prime-power expansion `∑_{𝔭, e} (w(𝔭) N(𝔭)⁻ᶻ) ^ (e + 1) / (e + 1)` of a logarithm of the
`L`-series of an ideal weight. -/
private noncomputable def powerSum (w : MultiplicativeIdealWeight K) (z : ℂ) : ℂ :=
  ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
    (w pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1)

variable {w : MultiplicativeIdealWeight K}

/-- A weight bounded by `1` gives an ideal arithmetic function bounded by `1`. -/
private theorem norm_toIdealArithmeticFunction_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1)
    (I : (Ideal (𝓞 K))⁰) : ‖w.toIdealArithmeticFunction I‖ ≤ 1 := by
  rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply]
  exact hw _

/-- A weight bounded by `1` has an absolutely convergent ideal series on `Re s > 1`. -/
private theorem summable_idealTerm_of_norm_le_one (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : Summable (idealTerm K w.toIdealArithmeticFunction s) :=
  summable_idealTerm_of_bounded_of_one_lt_re (norm_toIdealArithmeticFunction_le hw) hs

/-- For `t ≥ 1` the local ratio `w(𝔭) N(𝔭)⁻ᵗ` of a weight bounded by `1` is at most `N(𝔭)⁻¹`. -/
private theorem norm_div_absNorm_cpow_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1)
    (P : HeightOneSpectrum (𝓞 K)) {t : ℝ} (ht : 1 ≤ t) :
    ‖w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (t : ℂ)‖ ≤ (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
  have hN : (1 : ℝ) ≤ Ideal.absNorm P.asIdeal :=
    one_le_two.trans (two_le_absNorm_asIdeal_real P)
  have hpos : 0 < Ideal.absNorm P.asIdeal := by exact_mod_cast zero_lt_one.trans_le hN
  rw [norm_div, Complex.norm_natCast_cpow_of_pos hpos, Complex.ofReal_re, div_eq_mul_inv]
  calc ‖w P.asIdeal‖ * ((Ideal.absNorm P.asIdeal : ℝ) ^ t)⁻¹
      ≤ 1 * ((Ideal.absNorm P.asIdeal : ℝ) ^ (1 : ℝ))⁻¹ := by
        gcongr
        exact hw _
    _ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by rw [one_mul, Real.rpow_one]

/-- The majorant of the prime-power tail. -/
private theorem summable_tailBound :
    Summable fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      2 * ((Ideal.absNorm pe.1.asIdeal : ℝ)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ pe.2) := by
  have h2 := summable_absNorm_rpow_primes_of_one_lt (K := K) one_lt_two
  have h2' : Summable fun P : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm P.asIdeal : ℝ)⁻¹ ^ 2 :=
    h2.congr fun P ↦ by
      rw [Real.rpow_neg (Nat.cast_nonneg _), inv_pow, Real.rpow_two]
  exact ((h2'.mul_of_nonneg summable_geometric_two (fun _ ↦ by positivity)
    fun _ ↦ by positivity)).mul_left 2

/-- **The prime-power tail is bounded.** For a weight bounded by `1` and real `t > 1`, the
prime-power expansion differs from the prime sum by at most a constant independent of `t`. -/
private theorem norm_powerSum_sub_primeSum_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {t : ℝ}
    (ht : 1 < t) :
    ‖powerSum w t - primeSum w t‖ ≤ ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
      2 * ((Ideal.absNorm pe.1.asIdeal : ℝ)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ pe.2) := by
  classical
  have hs := summable_idealTerm_of_norm_le_one hw (s := t) (by simpa using ht)
  set r : HeightOneSpectrum (𝓞 K) → ℂ :=
    fun P ↦ w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (t : ℂ)
  have hr : Summable r := w.summable_div_of_summable_idealTerm hs
  have hT := Complex.summable_taylorSeries_neg_log hr (w.norm_div_lt_one_of_summable_idealTerm hs)
  set a : HeightOneSpectrum (𝓞 K) × ℕ → ℂ := fun pe ↦ r pe.1 ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1)
  set a₀ : HeightOneSpectrum (𝓞 K) × ℕ → ℂ := fun pe ↦ if pe.2 = 0 then a pe else 0
  have hinj : Function.Injective fun P : HeightOneSpectrum (𝓞 K) ↦ (P, 0) :=
    fun P Q h ↦ congrArg Prod.fst h
  have hsupp : Function.support a₀ ⊆ Set.range fun P : HeightOneSpectrum (𝓞 K) ↦ (P, 0) := by
    rintro ⟨P, e⟩ he
    by_cases h : e = 0
    · exact ⟨P, by rw [h]⟩
    · exact absurd (by simp [a₀, h]) he
  have ha₀ : ∀ P, a₀ (P, 0) = r P := fun P ↦ by simp [a₀, a]
  have hsum₀ : Summable a₀ := (hinj.summable_iff fun x hx ↦
    Function.notMem_support.mp fun h ↦ hx (hsupp h)).mp (by simpa [Function.comp_def, ha₀] using hr)
  have htsum₀ : ∑' pe, a₀ pe = primeSum w t := by
    rw [← hinj.tsum_eq hsupp]
    exact tsum_congr ha₀
  rw [powerSum, ← htsum₀, ← hT.tsum_sub hsum₀]
  refine tsum_of_norm_bounded summable_tailBound.hasSum fun ⟨P, e⟩ ↦ ?_
  have hN : (2 : ℝ) ≤ Ideal.absNorm P.asIdeal := two_le_absNorm_asIdeal_real P
  have hx := norm_div_absNorm_cpow_le hw P ht.le
  rcases e with _ | k
  · simp [a₀]
  · simp only [a₀, a, ite_eq_right (Nat.succ_ne_zero k), sub_zero]
    have hk : (1 : ℝ) ≤ ‖((k + 1 : ℕ) : ℂ) + 1‖ := by
      rw [← Nat.cast_add_one, Complex.norm_natCast]
      exact_mod_cast Nat.le_add_left 1 _
    have hNinv : (Ideal.absNorm P.asIdeal : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ two_pos hN
    calc ‖r P ^ (k + 1 + 1) / (((k + 1 : ℕ) : ℂ) + 1)‖
        ≤ ‖r P‖ ^ (k + 1 + 1) := by
          rw [norm_div, norm_pow]
          exact div_le_self (by positivity) hk
      _ ≤ (Ideal.absNorm P.asIdeal : ℝ)⁻¹ ^ (k + 1 + 1) := by gcongr
      _ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ ^ 2 * (Ideal.absNorm P.asIdeal : ℝ)⁻¹ ^ k := by ring
      _ ≤ (Ideal.absNorm P.asIdeal : ℝ)⁻¹ ^ 2 * (1 / 2) ^ k := by gcongr
      _ = 2 * ((Ideal.absNorm P.asIdeal : ℝ)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ (k + 1)) := by ring

/-- **A logarithm of a continued `L`-series stays bounded.** If the `L`-series of a weight
bounded by `1` agrees on `Re s > 1` with a function analytic and nonzero at `s = 1`, then its
prime-power expansion is bounded as `t → 1⁺`. -/
private theorem exists_norm_powerSum_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {C : ℂ → ℂ}
    (hC : AnalyticAt ℂ C 1) (hC1 : C 1 ≠ 0)
    (hCL : ∀ z : ℂ, 1 < z.re → C z = LSeries (normCoeff K w.toIdealArithmeticFunction) z) :
    ∃ B, ∀ᶠ t : ℝ in 𝓝[>] 1, ‖powerSum w t‖ ≤ B := by
  have hder (z : ℂ) (hz : 1 < z.re) : HasDerivAt (powerSum w) (logDeriv C z) z := by
    have habs := idealAbscissaOfAbsConv_lt_re_of_bounded (norm_toIdealArithmeticFunction_le hw) hz
    have h := w.hasDerivAt_tsum_prime_pow habs
    rw [← w.logDeriv_LSeries_eq_tsum_prime_pow habs] at h
    have heq : C =ᶠ[𝓝 z] LSeries (normCoeff K w.toIdealArithmeticFunction) :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
        fun y hy ↦ hCL y hy
    rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds, ← logDeriv_apply]
    exact h
  have hcont : ContinuousAt (logDeriv C) 1 := by
    have : logDeriv C = fun z ↦ deriv C z / C z := funext fun z ↦ logDeriv_apply C z
    rw [this]
    exact hC.deriv.continuousAt.div hC.continuousAt hC1
  set M := ‖logDeriv C 1‖ + 1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hcont.norm.eventually_lt continuousAt_const (lt_add_one ‖logDeriv C 1‖))
  set x₀ : ℝ := 1 + ε / 2
  have hx₀ : x₀ ∈ Set.Ioo (1 : ℝ) (1 + ε) := ⟨by simp [x₀, hε], by simp [x₀, hε]⟩
  refine ⟨‖powerSum w x₀‖ + M * ε, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + ε by linarith)] with t ht
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ ↦ powerSum w u) (f' := fun u : ℝ ↦ logDeriv C u)
    (fun u hu ↦ ((hder u (by simpa using hu.1)).comp_ofReal).hasDerivWithinAt)
    (fun u hu ↦ (hball (by
      rw [Complex.dist_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hu.1, hu.2])).le) (convex_Ioo _ _) hx₀ ht
  have hdist : ‖t - x₀‖ ≤ ε := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2, hx₀.1, hx₀.2]
  have hM : 0 ≤ M := by positivity
  calc ‖powerSum w t‖ ≤ ‖powerSum w x₀‖ + ‖powerSum w t - powerSum w x₀‖ := norm_le_insert' _ _
    _ ≤ ‖powerSum w x₀‖ + M * ε := by
        gcongr
        exact hmvt.trans (mul_le_mul_of_nonneg_left hdist hM)

/-- **The prime sum of a continued `L`-series stays bounded.** -/
private theorem exists_norm_primeSum_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {C : ℂ → ℂ}
    (hC : AnalyticAt ℂ C 1) (hC1 : C 1 ≠ 0)
    (hCL : ∀ z : ℂ, 1 < z.re → C z = LSeries (normCoeff K w.toIdealArithmeticFunction) z) :
    ∃ B, ∀ᶠ t : ℝ in 𝓝[>] 1, ‖primeSum w t‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_norm_powerSum_le hw hC hC1 hCL
  refine ⟨B + ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
      2 * ((Ideal.absNorm pe.1.asIdeal : ℝ)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ pe.2), ?_⟩
  filter_upwards [hB, self_mem_nhdsWithin] with t hBt (ht : 1 < t)
  calc ‖primeSum w t‖ ≤ ‖powerSum w t‖ + ‖powerSum w t - primeSum w t‖ := norm_le_insert _ _
    _ ≤ _ := add_le_add hBt (norm_powerSum_sub_primeSum_le hw ht)

open scoped Classical in
/-- The prime-ideal zeta sum of a set of primes, as a complex prime sum of its indicator. -/
private theorem ofReal_primeIdealZetaSum (S : Set (HeightOneSpectrum (𝓞 K))) (t : ℝ) :
    ((S.primeIdealZetaSum t : ℝ) : ℂ) = ∑' P : HeightOneSpectrum (𝓞 K),
      (if P ∈ S then 1 else 0) / (Ideal.absNorm P.asIdeal : ℂ) ^ (t : ℂ) := by
  rw [Set.primeIdealZetaSum_def,
    tsum_subtype S fun P ↦ (Ideal.absNorm P.asIdeal : ℝ) ^ (-t), Complex.ofReal_tsum]
  refine tsum_congr fun P ↦ ?_
  by_cases h : P ∈ S
  · simp [h, Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_cpow (Nat.cast_nonneg _)]
  · simp [h]

end PrimeSum

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

open scoped Classical IsMulCommutative in
/-- Character orthogonality at every prime, the ramified ones included: the character sum is
`#Gal(F/K)` on the Frobenius fibre of `σ` and `0` off it. -/
private theorem sum_inv_mul_galoisCharacterWeight_eq_ite [IsMulCommutative (F ≃ₐ[K] F)]
    (σ : F ≃ₐ[K] F) (P : HeightOneSpectrum (𝓞 K)) :
    ∑ χ : (F ≃ₐ[K] F) →* ℂˣ,
        (((χ σ)⁻¹ : ℂˣ) : ℂ) * MonoidHom.galoisCharacterWeight (L := F) χ P.asIdeal =
      if P ∈ frobeniusPrimeSet K F (ConjClasses.mk σ) then (Nat.card (F ≃ₐ[K] F) : ℂ) else 0 := by
  by_cases hP : P ∈ ramifiedPrimes K F
  · rw [AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_eq_zero_of_mem_ramifiedPrimes σ P hP,
      ite_eq_right fun h ↦
        frobeniusPrimeSet_subset_compl_ramifiedPrimes _ h (Finset.mem_coe.mpr hP)]
  · rw [mem_ramifiedPrimes_iff, not_not] at hP
    rw [AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_of_unramified σ P hP,
      mem_frobeniusPrimeSet_iff_artinSymbol_eq hP]
    have : P.asIdeal.IsMaximal := P.isMaximal
    generalize artinSymbol P.asIdeal hP = c
    have hc : ConjClasses.mk c.out = c := Quotient.out_eq c
    have key : c.out = σ ↔ c = ConjClasses.mk σ := ⟨fun h ↦ h ▸ hc.symm,
      fun h ↦ isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (hc.trans h))⟩
    by_cases h : c = ConjClasses.mk σ
    · rw [ite_eq_left (key.mpr h), ite_eq_left h]
    · rw [ite_eq_right (mt key.mp h), ite_eq_right h]

/-- The weight of a Galois character is bounded by `1`. -/
private theorem norm_galoisCharacterWeight_le (χ : (F ≃ₐ[K] F) →* ℂˣ) (I : Ideal (𝓞 K)) :
    ‖MonoidHom.galoisCharacterWeight (L := F) χ I‖ ≤ 1 := by
  simpa using χ.galoisCharacterUnitaryWeight.norm_le_one I

/-- The prime sum of the trivial character is the prime sum over the unramified primes. -/
private theorem primeSum_galoisCharacterWeight_one (t : ℝ) :
    primeSum (MonoidHom.galoisCharacterWeight (L := F) (1 : (F ≃ₐ[K] F) →* ℂˣ)) t =
      (((↑(ramifiedPrimes K F) : Set (HeightOneSpectrum (𝓞 K)))ᶜ.primeIdealZetaSum t : ℝ) : ℂ) := by
  classical
  rw [ofReal_primeIdealZetaSum, primeSum, MonoidHom.galoisCharacterWeight_one]
  refine tsum_congr fun P ↦ ?_
  rw [MultiplicativeIdealWeight.ofBadPrimes_apply, Ideal.isPrimeTo_asIdeal_iff, Set.mem_compl_iff]

open scoped Classical in
/-- **The Frobenius fibre by orthogonality.** For `F / K` abelian and `t > 1`, `#Gal(F/K)` times
the prime sum over the Frobenius fibre of `σ` is `∑ χ, χ(σ)⁻¹ P_χ(t)`. -/
private theorem natCard_mul_primeIdealZetaSum_eq [IsMulCommutative (F ≃ₐ[K] F)]
    (σ : F ≃ₐ[K] F) {t : ℝ} (ht : 1 < t) :
    (Nat.card (F ≃ₐ[K] F) : ℂ) *
        (((frobeniusPrimeSet K F (ConjClasses.mk σ)).primeIdealZetaSum t : ℝ) : ℂ) =
      ∑ χ : (F ≃ₐ[K] F) →* ℂˣ,
        (((χ σ)⁻¹ : ℂˣ) : ℂ) * primeSum (MonoidHom.galoisCharacterWeight (L := F) χ) t := by
  have hsum (χ : (F ≃ₐ[K] F) →* ℂˣ) : Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      MonoidHom.galoisCharacterWeight (L := F) χ P.asIdeal /
        (Ideal.absNorm P.asIdeal : ℂ) ^ (t : ℂ) :=
    (MonoidHom.galoisCharacterWeight χ).summable_div_of_summable_idealTerm
      (summable_idealTerm_of_norm_le_one (norm_galoisCharacterWeight_le K F χ) (by simpa using ht))
  simp only [primeSum, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun χ _ ↦ (hsum χ).mul_left _, ofReal_primeIdealZetaSum,
    ← tsum_mul_left]
  refine tsum_congr fun P ↦ ?_
  simp only [mul_div_assoc', ← Finset.sum_div, sum_inv_mul_galoisCharacterWeight_eq_ite]
  split_ifs <;> simp

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
  set n := Nat.card (F ≃ₐ[K] F)
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  set ℓ : ℝ → ℝ := fun t ↦ Real.log (1 / (t - 1))
  have hℓ : Tendsto ℓ (𝓝[>] 1) atTop := Real.tendsto_log_one_div_sub_atTop 1
  -- The normalized prime sum of each character tends to `1` for the trivial character and to
  -- `0` for the others.
  have hlim (χ : (F ≃ₐ[K] F) →* ℂˣ) : Tendsto
      (fun t : ℝ ↦ primeSum (MonoidHom.galoisCharacterWeight (L := F) χ) t / (ℓ t : ℂ))
      (𝓝[>] 1) (𝓝 (if χ = 1 then 1 else 0)) := by
    split_ifs with hχ
    · subst hχ
      have h1 := (Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one _ _).mp
        (hasDirichletDensity_compl_ramifiedPrimes K F)
      refine ((Complex.continuous_ofReal.tendsto _).comp h1).congr fun t ↦ ?_
      rw [Function.comp_apply, primeSum_galoisCharacterWeight_one, Complex.ofReal_div]
    · obtain ⟨B, hB⟩ := exists_norm_primeSum_le (norm_galoisCharacterWeight_le K F χ)
        (cyclotomicCharacterSeriesC_analyticAt_one K F m χ hχ)
        (cyclotomicCharacterSeriesC_ne_zero_at_one K F m χ hχ)
        fun z hz ↦ cyclotomicCharacterSeriesC_eq_LSeries K F χ hz
      refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := B)).div_atTop hℓ)
      filter_upwards [hB, hℓ.eventually_gt_atTop 0] with t hBt hℓt
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hℓt.le]
      exact div_le_div_of_nonneg_right hBt hℓt.le
  have hC := (tendsto_finsetSum Finset.univ fun χ _ ↦ (hlim χ).const_mul
    (((χ σ)⁻¹ : ℂˣ) : ℂ)).const_mul (1 / (n : ℂ))
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    MonoidHom.one_apply, inv_one, Units.val_one] at hC
  rw [Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one]
  have hre := (Complex.continuous_re.tendsto _).comp hC
  have key : ∀ᶠ t : ℝ in 𝓝[>] 1, (Complex.re ∘ fun t : ℝ ↦ 1 / (n : ℂ) *
      ∑ χ : (F ≃ₐ[K] F) →* ℂˣ, (((χ σ)⁻¹ : ℂˣ) : ℂ) *
        (primeSum (MonoidHom.galoisCharacterWeight (L := F) χ) t / (ℓ t : ℂ))) t =
      (frobeniusPrimeSet K F (ConjClasses.mk σ)).primeIdealZetaSum t / ℓ t := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 1 < t)
    simp only [Function.comp_apply, mul_div_assoc', ← Finset.sum_div,
      ← natCard_mul_primeIdealZetaSum_eq K F σ ht]
    rw [← mul_assoc, one_div_mul_cancel hn, one_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  convert hre.congr' key using 2
  simp [n]

end NumberField.Chebotarev
