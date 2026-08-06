/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The `q`-expansion principle at `∞`

The quantitative form the dimension formulas need: the first `N` coefficients of
`qExpansion h f` vanish exactly when the cusp function is `O(‖q‖ ^ N)` near `0`.

The two directions use different arguments. Forwards is the Taylor bound for an analytic
function whose first `N` Taylor coefficients vanish
(`HasFPowerSeriesAt.isBigO_sub_partialSum_pow`). Backwards is a Cauchy estimate, bounding
`cuspFunction h f z / z ^ (n + 1)` on a small circle.

## Main results

* `ModularFormClass.tendsto_atImInfty_valueAtInfty`: a modular form tends to its value at
  `∞` along `atImInfty`.
* `ModularFormClass.cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero` and
  `ModularFormClass.qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow`: the two directions
  of the principle.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/Modularforms/DimGenCongLevels/Auxiliary.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), where it is the analytic input to the dimension formulas.
-/

namespace ModularFormClass

open scoped Topology Real
open UpperHalfPlane Filter

section Tendsto

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} {F : Type*} [FunLike F ℍ ℂ]

/-- Values of a modular form tend to `valueAtInfty` along `atImInfty`. -/
public lemma tendsto_atImInfty_valueAtInfty [ModularFormClass F Γ k]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (valueAtInfty f)) := by
  have hAn := ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have ht : Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (cuspFunction h f 0)) := by
    refine Filter.Tendsto.congr (fun τ ↦ ?_)
      ((hAn.continuousAt.tendsto).comp (UpperHalfPlane.qParam_tendsto_atImInfty hh))
    simpa using (SlashInvariantFormClass.eq_cuspFunction (f := f) (h := h) τ hΓ hh.ne')
  simpa [UpperHalfPlane.cuspFunction_apply_zero hh hAn hper] using ht

end Tendsto

section BigO

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} {F : Type*} [FunLike F ℍ ℂ]

/-- If the first `N` `q`-coefficients vanish, then the cusp function is `O(‖q‖^N)` near `0`. -/
public lemma cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero
    [ModularFormClass F Γ k]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (N : ℕ)
    (hcoeff : ∀ n < N, (qExpansion h f).coeff n = 0) :
    cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N) := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hAn := ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ
  have hhol := ModularFormClass.holo f
  have hbdd := ModularFormClass.bdd_at_infty f
  have hFPS : HasFPowerSeriesAt (cuspFunction h f)
      (qExpansionFormalMultilinearSeries (F := F) h f) 0 :=
    (hasFPowerSeries_cuspFunction (F := F) f hh hAn
      (fun τ ↦ hasSum_qExpansion hh hper hhol hbdd τ)).hasFPowerSeriesAt
  have hps : (qExpansionFormalMultilinearSeries (F := F) h f).partialSum N = 0 := by
    ext q
    exact Finset.sum_eq_zero fun n hn ↦ by
      simp [hcoeff n (by simpa [Finset.mem_range] using hn)]
  simpa [zero_add, hps] using hFPS.isBigO_sub_partialSum_pow N
/-- **The converse**: if `cuspFunction h f = O(‖q‖^N)` near `0`, then
`(qExpansion h f).coeff n = 0` for every `n < N`.

By strong induction on `n`: once the earlier coefficients vanish, the `n`-th Taylor
polynomial collapses to its top term, so the Taylor bound of
`HasFPowerSeriesAt.isBigO_sub_partialSum_pow` combines with the hypothesis to make that term
`O(‖q‖^(n+1))` — which forces it to vanish. -/
public lemma qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow
    [ModularFormClass F Γ k]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {N n : ℕ} (hn : n < N)
    (hO : cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N)) :
    (qExpansion h f).coeff n = 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hAn := ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ
  have hFPS : HasFPowerSeriesAt (cuspFunction h f)
      (qExpansionFormalMultilinearSeries (F := F) h f) 0 :=
    (hasFPowerSeries_cuspFunction (F := F) f hh hAn
      (fun τ ↦ hasSum_qExpansion hh hper (ModularFormClass.holo f)
        (ModularFormClass.bdd_at_infty f) τ)).hasFPowerSeriesAt
  set p := qExpansionFormalMultilinearSeries (F := F) h f with hp
  suffices key : ∀ m, m < N → (qExpansion h f).coeff m = 0 from key n hn
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    -- the earlier coefficients vanish, so the `m`-th Taylor polynomial is its top term alone
    have hpart : ∀ y : ℂ, p.partialSum (m + 1) y = p m fun _ ↦ y := by
      intro y
      have hzero : ∀ j ∈ Finset.range m, (p j fun _ ↦ y) = 0 := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hcj : (qExpansion h f).coeff j = 0 := ih j hj' (hj'.trans hm)
        simp [hp, qExpansionFormalMultilinearSeries, hcj]
      rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
        Finset.sum_eq_zero hzero, zero_add]
    -- the hypothesis is a bound of order `N ≥ m + 1`, hence also of order `m + 1`
    have hOm : cuspFunction h f =O[𝓝 (0 : ℂ)] fun q : ℂ ↦ ‖q‖ ^ (m + 1) := by
      refine hO.trans (Asymptotics.IsBigO.of_bound 1 ?_)
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
      have hq1 : ‖q‖ < 1 := by simpa using hq
      simpa using pow_le_pow_of_le_one (norm_nonneg q) hq1.le hm
    have htop : (fun y : ℂ ↦ p m fun _ ↦ y) =O[𝓝 (0 : ℂ)] fun y : ℂ ↦ ‖y‖ ^ (m + 1) := by
      have hsub := hFPS.isBigO_sub_partialSum_pow (m + 1)
      simp only [zero_add, hpart] at hsub
      simpa using (hOm.sub hsub)
    have hone := htop.continuousMultilinearMap_apply_eq_zero 1
    have hco : p.coeff m = 0 := hone
    simpa [hp] using hco
end BigO

end ModularFormClass
