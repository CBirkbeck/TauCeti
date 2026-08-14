/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# `q`-coefficient vanishing and cusp-function growth

The dictionary between vanishing of the first `N` `q`-coefficients of a modular form and
`O(‖q‖^N)` growth of its cusp function at `0`, in both directions, together with the limit
of the form's values along `Im τ → ∞`. These are the analytic inputs of the norm step of
the general-level valence reduction: transporting coefficient vanishing through the norm
map to level one goes via the growth bound, which is multiplicative.

## Main declarations

* `TauCeti.ModularForm.modularForm_tendsto_valueAtInfty`: values of a modular form tend to
  `valueAtInfty` along `atImInfty`.
* `TauCeti.ModularForm.cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero`: if the first
  `N` `q`-coefficients vanish, the cusp function is `O(‖q‖^N)` near `0`.
* `TauCeti.ModularForm.qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow`: conversely,
  an `O(‖q‖^N)` bound kills the `n`-th coefficient for every `n < N`.

## References

Ported from AINTLIB's `LeanModularForms` project
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), commit `2baa76f742`,
Apache 2.0, the file
`projects/LeanModularForms/LeanModularForms/Modularforms/DimGenCongLevels/Auxiliary.lean`),
with the converse direction reproved through Mathlib's power-series uniqueness machinery
instead of the source's circle-integral bounds.
-/

namespace TauCeti.ModularForm

open scoped Topology Real
open UpperHalfPlane Filter

noncomputable section

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} {F : Type*} [FunLike F ℍ ℂ]

/-- Values of a modular form tend to `valueAtInfty` along `atImInfty`. -/
public lemma modularForm_tendsto_valueAtInfty [ModularFormClass F Γ k]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (valueAtInfty f)) := by
  have hAn := ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have ht : Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (cuspFunction h f 0)) := by
    refine Filter.Tendsto.congr (fun τ ↦ ?_)
      ((hAn.continuousAt.tendsto).comp (UpperHalfPlane.qParam_tendsto_atImInfty hh))
    simpa using (SlashInvariantFormClass.eq_cuspFunction (f := f) (h := h) τ hΓ hh.ne')
  simpa [UpperHalfPlane.cuspFunction_apply_zero hh hAn hper] using ht

/-- If the first `N` `q`-coefficients vanish, then the cusp function is `O(‖q‖^N)` near
`0`. -/
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

/-- If `cuspFunction h f = O(‖q‖^N)` near `0`, then the `n`-th `q`-coefficient vanishes for
`n < N`: by strong induction the partial sum of order `n + 1` reduces to the `n`-th
homogeneous term, which is then dominated by `‖q‖ ^ (n + 1)` and must vanish. -/
public lemma qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow
    [ModularFormClass F Γ k]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {N n : ℕ} (hn : n < N)
    (hO : cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N)) :
    (qExpansion h f).coeff n = 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hFPS : HasFPowerSeriesAt (cuspFunction h f)
      (qExpansionFormalMultilinearSeries (F := F) h f) 0 :=
    (hasFPowerSeries_cuspFunction (F := F) f hh
      (ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ)
      (fun τ ↦ hasSum_qExpansion hh hper (ModularFormClass.holo f)
        (ModularFormClass.bdd_at_infty f) τ)).hasFPowerSeriesAt
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hON : cuspFunction h f =O[𝓝 (0 : ℂ)] fun q : ℂ ↦ ‖q‖ ^ (n + 1) := by
    refine hO.trans (Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩)
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    simpa [abs_of_nonneg (norm_nonneg q)] using
      pow_le_pow_of_le_one (norm_nonneg q) (mem_ball_zero_iff.mp hq).le hn
  have hps : ∀ y : ℂ,
      (qExpansionFormalMultilinearSeries (F := F) h f).partialSum (n + 1) y =
        y ^ n • (qExpansion h f).coeff n := by
    intro y
    rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_eq_zero
      (fun m hm ↦ by
        simp [ih m (Finset.mem_range.mp hm) ((Finset.mem_range.mp hm).trans hn)]),
      zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      qExpansionFormalMultilinearSeries_coeff]
  have hhom : (fun y : ℂ ↦ qExpansionFormalMultilinearSeries (F := F) h f n fun _ ↦ y)
      =O[𝓝 (0 : ℂ)] fun y : ℂ ↦ ‖y‖ ^ (n + 1) := by
    have hsub := hFPS.isBigO_sub_partialSum_pow (n + 1)
    simp only [zero_add] at hsub
    refine (hON.sub hsub).congr_left fun y ↦ ?_
    rw [hps, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      qExpansionFormalMultilinearSeries_coeff]
    ring
  simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    qExpansionFormalMultilinearSeries_coeff] using
    hhom.continuousMultilinearMap_apply_eq_zero 1

end

end TauCeti.ModularForm
