/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cancellation
import TauCeti.Analysis.SpecialFunctions.Log.OneDivSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Basic
import TauCeti.NumberTheory.Chebotarev.Density.SplitsCompletely
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.CyclotomicSurjective
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Orthogonality

/-!
# The continued L-series of a cyclotomic Galois character

For a finite Galois extension `F / K` of number fields and a character `χ` of `Gal(F/K)`,
`cyclotomicCharacterSeriesC K F χ` is a holomorphic continuation of the `L`-series of the ideal
weight `galoisCharacterWeight χ` to the half-plane `Re s > 1 - 1 / [K : ℚ]`, when one exists. For
every `χ` it agrees with the `L`-series on `Re s > 1`.

For a cyclotomic extension `F = K(μ_m)` and a nontrivial character `χ`, the continuation exists,
so the series is analytic at `s = 1`, and its value at `s = 1` is nonzero.

## Main definitions

* `NumberField.Chebotarev.cyclotomicCharacterSeriesC`: the continued `L`-series of a Galois
  character.

## Main results

* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_eq_LSeries`: on `Re s > 1` it is the
  `L`-series of `galoisCharacterWeight χ`.
* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_analyticAt_one`: for `F = K(μ_m)` and `χ`
  nontrivial it is analytic at `s = 1`.
* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_ne_zero_at_one`: for `F = K(μ_m)` and `χ`
  nontrivial it is nonzero at `s = 1`.
-/

public section

open Filter IsDedekindDomain NumberField TauCeti TauCeti.GlobalNumberFields
open scoped NumberField Topology

namespace NumberField.Chebotarev

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

open scoped Classical in
/-- **The continued `L`-series of a Galois character.** The holomorphic continuation of the
`L`-series of `galoisCharacterWeight χ` from `Re s > 1` to the half-plane
`Re s > 1 - 1 / [K : ℚ]`, when such a continuation exists; otherwise the partial-summation
integral `continuedLFunctionOfWeight` of the weight. -/
noncomputable def cyclotomicCharacterSeriesC (χ : (F ≃ₐ[K] F) →* ℂˣ) : ℂ → ℂ :=
  if h : ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
        ∀ s : ℂ, 1 < s.re →
          f s = LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s
  then h.choose
  else continuedLFunctionOfWeight χ.galoisCharacterUnitaryWeight

variable {K F}

variable (K F) in
/-- **The continued `L`-series is the `L`-series on `Re s > 1`.** -/
theorem cyclotomicCharacterSeriesC_eq_LSeries (χ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    cyclotomicCharacterSeriesC K F χ s =
      LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s := by
  rw [cyclotomicCharacterSeriesC]
  split_ifs with h
  · exact h.choose_spec.2 s hs
  · rw [continuedLFunctionOfWeight_eq_LSeries _ hs,
      UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
      MonoidHom.val_galoisCharacterUnitaryWeight]

/-- The half-plane `Re s > 1 - 1 / [K : ℚ]` lies in `Re s > 0`. -/
private theorem re_pos_of_mem_halfPlane {s : ℂ} (hs : 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re) :
    0 < s.re := by
  have hd : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have : 1 / (Module.finrank ℚ K : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hd
  linarith

/-- On `Re s > 0` a local factor `1 - χ(𝔭) N(𝔭) ^ (-s)` of a unitary weight is nonzero. -/
private theorem one_sub_div_absNorm_cpow_ne_zero (w : UnitaryIdealWeight K)
    (𝔭 : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    1 - w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s ≠ 0 := by
  have hlt : ‖w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s‖ < 1 := by
    rw [norm_div, div_lt_one (zero_lt_one.trans (𝔭.one_lt_norm_absNorm_cpow hs))]
    exact (w.norm_le_one _).trans_lt (𝔭.one_lt_norm_absNorm_cpow hs)
  intro h
  rw [← sub_eq_zero.mp h, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- **The continuation exists for a nontrivial ray class character.** For `F = K(μ_m)` and a
character `χ` of `Gal(F/K)` with `χ ∘ cyclotomicArtin K F m` nontrivial, the `L`-series of the
weight of `χ` has a holomorphic continuation to `Re s > 1 - 1 / [K : ℚ]`. -/
private theorem exists_differentiableOn_eq_LSeries (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ.comp (cyclotomicArtin K F m) ≠ 1) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        f s = LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s := by
  set S := (cyclotomicModulus K m).support
  set w := χ.galoisCharacterUnitaryWeight
  have hcorr : Differentiable ℂ
      fun s : ℂ ↦ ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) :=
    Differentiable.fun_finsetProd fun 𝔭 _ ↦ (differentiable_const 1).sub
      ((differentiable_const _).div (differentiable_id.const_cpow (.inl 𝔭.natCast_absNorm_ne_zero))
        fun s ↦ by simp [Complex.cpow_eq_zero_iff, 𝔭.natCast_absNorm_ne_zero])
  have hne {s : ℂ} (hs : 0 < s.re) :
      ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun 𝔭 _ ↦ one_sub_div_absNorm_cpow_ne_zero w 𝔭 hs
  -- The continued `L`-function with the Euler factors at the primes dividing `m` deleted has
  -- cancellation; dividing by those factors, which are nonzero on `Re s > 0`, restores them.
  refine ⟨fun s ↦ continuedLFunctionOfWeight (w.restrict (S : Set _) S.finite_toSet) s /
      ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s), ?_, fun s hs ↦ ?_⟩
  · exact (differentiableOn_continuedLFunctionOfWeight
      (MonoidHom.hasCancellation_restrict_galoisCharacterUnitaryWeight χ hχ)).div
        hcorr.differentiableOn fun s hs ↦ hne (re_pos_of_mem_halfPlane hs)
  · dsimp only
    rw [continuedLFunctionOfWeight_restrict_of_one_lt_re w S hs,
      mul_div_cancel_right₀ _ (hne (by linarith)), continuedLFunctionOfWeight_eq_LSeries _ hs,
      UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
      MonoidHom.val_galoisCharacterUnitaryWeight]

/-- For `F = K(μ_m)` and `χ` nontrivial, the continued `L`-series is holomorphic on the half-plane
`Re s > 1 - 1 / [K : ℚ]`. -/
private theorem differentiableOn_cyclotomicCharacterSeriesC (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (cyclotomicCharacterSeriesC K F χ)
      {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := by
  -- The Artin map is surjective, so `χ ∘ cyclotomicArtin K F m` is nontrivial.
  have hχ' : χ.comp (cyclotomicArtin K F m) ≠ 1 := fun h ↦ hχ <|
    (MonoidHom.cancel_right (cyclotomicArtin_surjective K F m)).mp
      (h.trans (MonoidHom.one_comp _).symm)
  have h := exists_differentiableOn_eq_LSeries m χ hχ'
  rw [cyclotomicCharacterSeriesC]
  split_ifs
  exact h.choose_spec.1

variable (K F) in
/-- **Analyticity at `s = 1`.** For `F = K(μ_m)` and a nontrivial character `χ` of `Gal(F/K)`,
the continued `L`-series of `χ` is analytic at `s = 1`. -/
theorem cyclotomicCharacterSeriesC_analyticAt_one (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) :
    AnalyticAt ℂ (cyclotomicCharacterSeriesC K F χ) 1 :=
  (differentiableOn_cyclotomicCharacterSeriesC m χ hχ).analyticAt <|
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simpa using cancellationExponent_lt_one (K := K))

/-- **The completely split primes have a divergent prime sum.** As `s → 1⁺`, the prime sum over the
primes of `K` that split completely in `F` tends to infinity. -/
private theorem tendsto_primeIdealZetaSum_frobeniusPrimeSet_one_atTop :
    Tendsto (fun σ : ℝ ↦ (frobeniusPrimeSet K F 1).primeIdealZetaSum σ) (𝓝[>] 1) atTop := by
  have hd := (Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one _ _).mp
    (hasDirichletDensity_frobeniusPrimeSet_one K F)
  have hlog := Real.tendsto_log_one_div_sub_atTop 1
  refine (hd.pos_mul_atTop (by simp [Module.finrank_pos]) hlog).congr' ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with σ hσ
  exact div_mul_cancel₀ _ hσ.ne'

/-- The character sum of a power of the Galois weights at a prime is a nonnegative real number, and
at a completely split prime the sum of the weights themselves is `#Gal(F/K)`. -/
private theorem exists_sum_galoisCharacterWeight_pow_eq [IsMulCommutative (F ≃ₐ[K] F)]
    [Fintype ((F ≃ₐ[K] F) →* ℂˣ)] (P : HeightOneSpectrum (𝓞 K)) (j : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ ψ : (F ≃ₐ[K] F) →* ℂˣ, ψ.galoisCharacterWeight P.asIdeal ^ (j + 1) = r ∧
      (P ∈ frobeniusPrimeSet K F 1 → j = 0 → r = Nat.card (F ≃ₐ[K] F)) := by
  classical
  by_cases hP : P ∈ ramifiedPrimes K F
  · refine ⟨0, le_rfl, ?_, fun h _ ↦ absurd (Finset.mem_coe.mpr hP)
      (frobeniusPrimeSet_subset_compl_ramifiedPrimes 1 h)⟩
    simp [(MonoidHom.galoisCharacterWeight_apply_eq_zero_iff _ P).mpr hP]
  · rw [mem_ramifiedPrimes_iff, not_not] at hP
    have : P.asIdeal.IsMaximal := P.isMaximal
    have h := AlgEquiv.sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified
      (1 : F ≃ₐ[K] F) P hP (j + 1)
    simp only [map_one, inv_one, Units.val_one, one_mul] at h
    refine ⟨if (artinSymbol P.asIdeal hP).out ^ (j + 1) = 1 then Nat.card (F ≃ₐ[K] F) else 0,
      by positivity, ?_, fun h1 hj ↦ ?_⟩
    · convert h using 1
      · exact Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _) fun _ _ ↦ rfl
      · split_ifs <;> simp
    · subst hj
      have hout : (artinSymbol P.asIdeal hP).out = 1 := by
        have h1 := (mem_frobeniusPrimeSet_iff_artinSymbol_eq hP 1).mp h1
        exact isConj_one_right.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
          ((Quotient.out_eq _).trans (h1.trans ConjClasses.one_eq_mk_one)).symm)
      simp [hout]

open scoped Classical in
/-- **The product of all the character `L`-series is unbounded at `s = 1⁺`.** For `F / K` abelian,
the product over all characters `ψ` of `Gal(F/K)` of the `L`-series of `galoisCharacterWeight ψ`
tends to infinity in norm as `s → 1⁺` along the reals. -/
private theorem tendsto_norm_prod_LSeries_atTop [IsMulCommutative (F ≃ₐ[K] F)] :
    Tendsto (fun σ : ℝ ↦ ‖∏ ψ : (F ≃ₐ[K] F) →* ℂˣ,
      LSeries (normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction) σ‖)
      (𝓝[>] 1) atTop := by
  -- The Euler-product logarithms of all the `L`-series sum to a series of nonnegative reals,
  -- which dominates `#Gal(F/K)` times the prime sum over the completely split primes.
  choose r hr0 hr hrn using exists_sum_galoisCharacterWeight_pow_eq (K := K) (F := F)
  set n : ℕ := Nat.card (F ≃ₐ[K] F)
  -- The real series `∑_{P, e} r(P, e) / (N(P) ^ σ) ^ (e + 1) / (e + 1)`.
  let ρ : ℝ → HeightOneSpectrum (𝓞 K) × ℕ → ℝ := fun σ pe ↦
    r pe.1 pe.2 / ((Ideal.absNorm pe.1.asIdeal : ℝ) ^ σ) ^ (pe.2 + 1) / (pe.2 + 1)
  have hρ0 (σ : ℝ) (pe) : 0 ≤ ρ σ pe := by
    have := hr0 pe.1 pe.2
    positivity
  have key (σ : ℝ) (hσ : 1 < σ) : Summable (ρ σ) ∧ ‖∏ ψ : (F ≃ₐ[K] F) →* ℂˣ,
      LSeries (normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction) σ‖ =
        Real.exp (∑' pe, ρ σ pe) := by
    have hs (ψ : (F ≃ₐ[K] F) →* ℂˣ) :
        Summable (idealTerm K ψ.galoisCharacterWeight.toIdealArithmeticFunction σ) := by
      have := summable_idealTerm_of_unitary_of_one_lt_re ψ.galoisCharacterUnitaryWeight
        (s := σ) (by simpa using hσ)
      rwa [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
        MonoidHom.val_galoisCharacterUnitaryWeight] at this
    have hT (ψ : (F ≃ₐ[K] F) →* ℂˣ) := Complex.summable_taylorSeries_neg_log
      (ψ.galoisCharacterWeight.summable_div_of_summable_idealTerm (hs ψ))
      (ψ.galoisCharacterWeight.norm_div_lt_one_of_summable_idealTerm (hs ψ))
    have hterm (pe : HeightOneSpectrum (𝓞 K) × ℕ) :
        ∑ ψ : (F ≃ₐ[K] F) →* ℂˣ, (ψ.galoisCharacterWeight pe.1.asIdeal /
          (Ideal.absNorm pe.1.asIdeal : ℂ) ^ (σ : ℂ)) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1) =
          (ρ σ pe : ℂ) := by
      simp only [div_pow, ← Finset.sum_div, hr, ρ]
      push_cast
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    have hsum : Summable fun pe ↦ (ρ σ pe : ℂ) :=
      (summable_sum fun ψ _ ↦ hT ψ).congr hterm
    refine ⟨Complex.summable_ofReal.mp hsum, ?_⟩
    simp_rw [← MultiplicativeIdealWeight.exp_tsum_prime_pow_eq_LSeries _ (hs _),
      ← Complex.exp_sum, ← Summable.tsum_finsetSum fun ψ _ ↦ hT ψ, hterm,
      ← Complex.ofReal_tsum, Complex.norm_exp_ofReal]
  refine tendsto_atTop_mono' _ ?_
    ((tendsto_primeIdealZetaSum_frobeniusPrimeSet_one_atTop (K := K) (F := F)).const_mul_atTop
      (Nat.cast_pos.mpr Nat.card_pos : (0 : ℝ) < n))
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  obtain ⟨hρ, hnorm⟩ := key σ hσ
  rw [hnorm, Set.primeIdealZetaSum_def, ← tsum_mul_left]
  refine le_trans ?_ ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
  refine le_of_eq_of_le ?_ (tsum_comp_le_tsum_of_inj hρ (hρ0 σ)
    (i := fun P : frobeniusPrimeSet K F 1 ↦ (P.1, 0)) fun P Q h ↦ Subtype.ext (congrArg Prod.fst h))
  refine tsum_congr fun P ↦ ?_
  simp only [Function.comp_apply, ρ, hrn P.1 0 P.2 rfl, zero_add, pow_one, Nat.cast_zero,
    Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv, inv_one, mul_one]

variable (K F) in
/-- **Nonvanishing at `s = 1`.** For `F = K(μ_m)` and a nontrivial character `χ` of `Gal(F/K)`,
the continued `L`-series of `χ` does not vanish at `s = 1`. -/
theorem cyclotomicCharacterSeriesC_ne_zero_at_one (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) :
    cyclotomicCharacterSeriesC K F χ 1 ≠ 0 := by
  classical
  intro h0
  have := IsCyclotomicExtension.isMulCommutative {m} K F
  set L : ((F ≃ₐ[K] F) →* ℂˣ) → ℝ → ℂ := fun ψ σ ↦
    LSeries (normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction) σ
  have hray : Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
      exact Set.mem_compl_singleton_iff.mpr (by exact_mod_cast hσ.ne')
  have hL (ψ : (F ≃ₐ[K] F) →* ℂˣ) :
      ∀ᶠ σ : ℝ in 𝓝[>] 1, cyclotomicCharacterSeriesC K F ψ σ = L ψ σ := by
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    exact cyclotomicCharacterSeriesC_eq_LSeries K F ψ (by simpa using hσ)
  -- The product of all the `L`-series is unbounded as `σ → 1⁺`. But the trivial character's
  -- series times `σ - 1` converges, the series of `χ` divided by `σ - 1` converges since it
  -- vanishes at `1`, and the other series converge, so the product converges.
  let c : ((F ≃ₐ[K] F) →* ℂˣ) → ℝ → ℂ := fun ψ σ ↦
    Pi.mulSingle (M := fun _ ↦ ℂ) 1 ((σ : ℂ) - 1) ψ *
      Pi.mulSingle (M := fun _ ↦ ℂ) χ ((σ : ℂ) - 1)⁻¹ ψ
  have hlim (ψ : (F ≃ₐ[K] F) →* ℂˣ) : ∃ z, Tendsto (fun σ ↦ c ψ σ * L ψ σ) (𝓝[>] 1) (𝓝 z) := by
    by_cases h1 : ψ = 1
    · subst h1
      refine ⟨_, (tendsto_sub_one_mul_LSeries_ofBadPrimes (ramifiedPrimes K F)).congr' ?_⟩
      refine Eventually.of_forall fun σ ↦ ?_
      simp [c, L, Pi.mulSingle_apply, Ne.symm hχ]
    have hana := cyclotomicCharacterSeriesC_analyticAt_one K F m ψ h1
    by_cases h2 : ψ = χ
    · subst h2
      refine ⟨_, ((hasDerivAt_iff_tendsto_slope.mp hana.differentiableAt.hasDerivAt).comp
        hray).congr' ?_⟩
      filter_upwards [hL ψ] with σ hσ
      simp [c, slope_def_field, Pi.mulSingle_apply, h0, hσ, h1, div_eq_inv_mul]
    · refine ⟨_, (hana.continuousAt.tendsto.comp (hray.mono_right nhdsWithin_le_nhds)).congr' ?_⟩
      filter_upwards [hL ψ] with σ hσ
      simp [c, Pi.mulSingle_apply, h1, h2, hσ]
  choose z hz using hlim
  refine not_tendsto_atTop_of_tendsto_nhds (tendsto_finsetProd Finset.univ fun ψ _ ↦ hz ψ).norm
    ((tendsto_norm_prod_LSeries_atTop (K := K) (F := F)).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  have hσ1 : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hσ.ne')
  have hc : ∏ ψ, c ψ σ = 1 := by
    simp only [c, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.mem_univ,
      ↓reduceIte, mul_inv_cancel₀ hσ1]
  rw [Finset.prod_mul_distrib, hc, one_mul]

end NumberField.Chebotarev
