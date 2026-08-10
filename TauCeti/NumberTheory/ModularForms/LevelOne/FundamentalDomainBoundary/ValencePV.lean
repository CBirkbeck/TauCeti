/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ExcisedAssembly
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ExcisedIntegrability
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ArcExcisionMeasure
public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.On
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.LogDerivPV

/-!
# The boundary principal value of a level-one logarithmic derivative

`intervalIntegral_excised_logDeriv_fdBoundary` assembles the boundary integral at a **fixed**
`ε`, as `2πi·ord_∞ − (k/2)·∫₁³ (excised logDeriv γ)`. Two further facts turn that into a
principal value:

* the excised integrand is integrable for every `ε` (`ExcisedIntegrability`), so the assembly's
  assumed hypotheses hold, and the first clause of `HasCauchyPVWith` is immediate;
* the arc term converges, to `(π/3)·I` (`ArcExcisionMeasure`).

So the excised integrals converge, and the limit is `2πi·ord_∞ − k·(π/6)·I` — the same constant
the *unexcised* assembly produces, as it must be, since the excision only buys tolerance of zeros
on the contour.

## Main results

* `TauCeti.ModularForm.hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex`: the boundary
  principal value of `logDeriv (f ∘ ofComplex)` is `2πi·ord_∞ − k·(π/6)·I`.
* `TauCeti.ModularForm.two_pi_I_mul_sum_windingNumber_mul_order_eq`: equating that with the
  argument principle gives `2πi·Σ n_z·ord z = 2πi·ord_∞ − k·(π/6)·I`, the analytic identity the
  valence formula rests on.
-/

public section

open Complex Filter Function MeasureTheory Set Topology UpperHalfPlane

open scoped MatrixGroups Real

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- Each excision centre sits strictly below the ceiling, so once `ε` is small enough every
centre's `ε`-neighbourhood does too. -/
private theorem eventually_forall_im_add_lt {H : ℝ} {S : Finset ℂ} (hHgt : ∀ s ∈ S, s.im < H) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s ∈ S, s.im + ε < H := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · filter_upwards with ε using by simp
  · have hpos : (0 : ℝ) < S.inf' hne fun s => H - s.im :=
      (Finset.lt_inf'_iff _).2 fun s hs => sub_pos.mpr (hHgt s hs)
    filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε s hs
    have := hε.2.trans_le (Finset.inf'_le (fun s => H - s.im) hs)
    linarith

/-- The fixed-`ε` assembly, packaged as an eventual identity: for all small `ε` the excised
boundary integral is `2πi·ord_∞` minus `(k/2)` times the excised arc integral. The two
`ε`-dependent side conditions of the assembly are supplied here from their `ε`-free sources. -/
private theorem eventually_intervalIntegral_excised_eq [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ} {U : Set ℂ} (hH : 1 ≤ H)
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S) (hHgt : ∀ s ∈ S, s.im < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in (0 : ℝ)..5, if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
          else logDeriv (⇑f ∘ ofComplex) (fdBoundary H t) * deriv (fdBoundary H) t) =
        2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
          (k : ℂ) / 2 * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
            else logDeriv (fdBoundary H) t) := by
  have hside : ∀ {ε t : ℝ}, 0 < ε → ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) → t ∈ Icc (0 : ℝ) 5 →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0 := by
    intro ε t hε hex ht
    refine hoff _ (hUdom (fdBoundary_mem_coe_truncatedFundamentalDomain hH ht)) fun hs => hex ?_
    exact ⟨_, hs, by rw [sub_self, norm_zero]; exact hε.le⟩
  filter_upwards [eventually_forall_im_add_lt hHgt, self_mem_nhdsWithin] with ε hlt hε
  simpa only [smul_eq_mul, mul_comm] using
    intervalIntegral_excised_logDeriv_fdBoundary f hS hnorm hinv hlt hper
      (fun t ht hex =>
        (hside hε hex ⟨by linarith [ht.1], by linarith [ht.2]⟩).1.differentiableAt)
      (fun t ht hex => (hside hε hex ⟨by linarith [ht.1], by linarith [ht.2]⟩).2)
      hga hgz
      (intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary hH hε hUdom hoff
        (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact Icc_subset_Icc le_rfl (by norm_num)))
      (intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary hH hε hUdom hoff
        (by rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
            exact Icc_subset_Icc (by norm_num) (by norm_num)))
      (intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary hH hε hUdom hoff
        (by rw [uIcc_of_le (by norm_num : (4 : ℝ) ≤ 5)]
            exact Icc_subset_Icc (by norm_num) le_rfl))

/-- **The boundary principal value of a level-one logarithmic derivative.** The excised integrals
converge as `ε → 0⁺`, to `2πi·ord_∞ − k·(π/6)·I`.

The hypotheses are those of the fixed-`ε` assembly, with the two `ε`-dependent ones replaced by
their `ε`-free sources: `hHgt` (each excision centre sits below the ceiling) gives `hlt` once `ε`
is small, and `hoff` (analytic and nonvanishing off the centres on an open `U` containing the
truncated fundamental domain) gives the differentiability and nonvanishing side conditions at
every `ε`, as well as the integrability. -/
theorem hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ} {U : Set ℂ} (hH : 1 ≤ H)
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S) (hHgt : ∀ s ∈ S, s.im < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    Contour.HasCauchyPVWith (fdBoundary H) 0 5 (logDeriv (⇑f ∘ ofComplex)) S
      (2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I)) := by
  refine Contour.hasCauchyPVWith_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [smul_eq_mul, mul_comm] using
      intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary hH hε hUdom hoff
        (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)])
  · refine Tendsto.congr' (Filter.EventuallyEq.symm
      (eventually_intervalIntegral_excised_eq f hS hH hnorm hinv hHgt hper hUdom hoff hga hgz)) ?_
    have hval : 2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) / 2 * ((Real.pi / 3 : ℝ) * Complex.I) =
        2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
          (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I) := by
      push_cast
      ring
    exact hval ▸ (tendsto_const_nhds.sub
      ((tendsto_intervalIntegral_excised_logDeriv_fdBoundary_arc H S).const_mul _))

/-- **The weighted zero count equals the cusp order minus the weight term.** Both sides are the
same Cauchy principal value along the boundary contour: `hasCauchyPV_fdBoundary_logDeriv`
evaluates it by the argument principle, as `2πi` times the winding-weighted sum of orders, while
`hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex` evaluates it by the excised assembly, as
`2πi·ord_∞ − k·(π/6)·I`. Principal values are unique — even across different excision sets — so
the two agree.

This is the analytic identity the valence formula rests on: dividing by `2πi` and reading off the
corner winding numbers (`½` at `i`, `1/6` at each `ρ`-corner) turns it into
`ord_∞ + ½·ord_i + ⅓·ord_ρ + Σ ord_q = k/12`. -/
theorem two_pi_I_mul_sum_windingNumber_mul_order_eq [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ} {U : Set ℂ} {ord : ℂ → ℤ} (hH : 1 ≤ H)
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S) (hHgt : ∀ s ∈ S, s.im < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1) (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt (⇑f ∘ ofComplex) s)
    (hord : ∀ s ∈ S, s ∈ U → meromorphicOrderAt (⇑f ∘ ofComplex) s = (ord s : WithTop ℤ))
    (hbase : fdBoundary H 0 ∉ (S : Set ℂ))
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    2 * (Real.pi : ℂ) * Complex.I *
        ∑ z ∈ S, Contour.windingNumber (fdBoundary H) 0 5 z * (ord z : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I) :=
  (hasCauchyPV_fdBoundary_logDeriv hH hU hUdom hoff hmero hord hbase).unique
    (hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex f hS hH hnorm hinv hHgt hper hUdom
      hoff hga hgz).hasCauchyPV


/-- **The weighted zero count in terms of `orderOfVanishingAt`.** The abstract order function of
`two_pi_I_mul_sum_windingNumber_mul_order_eq` is the modular-forms order at each point of the
excision set, once the excision points are recorded as points of the upper half plane.

`orderOfVanishingAt` is by definition the meromorphic order of `f ∘ ofComplex`
(`orderOfVanishingAt_def`), so the abstract `hord` hypothesis is discharged by `rfl` at every
point whose order is finite — which is what `hfin` records. -/
theorem two_pi_I_mul_sum_windingNumber_mul_orderOfVanishingAt_eq
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ}
    {U : Set ℂ} (hH : 1 ≤ H) (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hHgt : ∀ s ∈ S, s.im < H) (hper : Periodic (⇑f ∘ ofComplex) 1) (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt (⇑f ∘ ofComplex) s)
    (hfin : ∀ s ∈ S, s ∈ U → meromorphicOrderAt (⇑f ∘ ofComplex) s ≠ ⊤)
    (hbase : fdBoundary H 0 ∉ (S : Set ℂ))
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    2 * (Real.pi : ℂ) * Complex.I *
        ∑ z ∈ S, Contour.windingNumber (fdBoundary H) 0 5 z *
          ((meromorphicOrderAt (⇑f ∘ ofComplex) z).untop₀ : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I) :=
  two_pi_I_mul_sum_windingNumber_mul_order_eq f hS hH hnorm hinv hHgt hper hU hUdom hoff hmero
    (fun s hsS hsU => (WithTop.coe_untop₀_of_ne_top (hfin s hsS hsU)).symm)
    hbase hga hgz


/-- **The valence identity, divided through.** Cancelling the common factor `2πi` from
`two_pi_I_mul_sum_windingNumber_mul_orderOfVanishingAt_eq` puts it in the shape the valence
formula is usually written in: the winding-weighted count of orders inside the contour equals the
cusp order minus `k/12`.

The weight term matches because `k·(π/6)·I = 2πi·(k/12)`. -/
theorem sum_windingNumber_mul_orderOfVanishingAt_eq [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ} {U : Set ℂ} (hH : 1 ≤ H)
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S) (hHgt : ∀ s ∈ S, s.im < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1) (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt (⇑f ∘ ofComplex) s)
    (hfin : ∀ s ∈ S, s ∈ U → meromorphicOrderAt (⇑f ∘ ofComplex) s ≠ ⊤)
    (hbase : fdBoundary H 0 ∉ (S : Set ℂ))
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    ∑ z ∈ S, Contour.windingNumber (fdBoundary H) 0 5 z *
        ((meromorphicOrderAt (⇑f ∘ ofComplex) z).untop₀ : ℂ) =
      qExpansionOrderAtCusp 1 ⇑f - (k : ℂ) / 12 := by
  have hne : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero]
  refine mul_left_cancel₀ hne ?_
  rw [two_pi_I_mul_sum_windingNumber_mul_orderOfVanishingAt_eq f hS hH hnorm hinv hHgt hper hU
    hUdom hoff hmero hfin hbase hga hgz]
  push_cast
  ring


end ModularForm

end TauCeti
