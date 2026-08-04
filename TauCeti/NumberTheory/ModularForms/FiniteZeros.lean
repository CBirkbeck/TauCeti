/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.OrderOfVanishing

/-!
# Finite zeros of a level-one modular form in the fundamental domain

A nonzero level-one modular form does not vanish above some height, since its cusp
function is nonvanishing on a punctured `q`-ball; its remaining nonzero-order points in
the standard fundamental domain lie in a truncated fundamental domain, which is compact,
so by the accumulation-point argument and the identity theorem they are finite — the
finite-support input to the valence formula.

## Main declarations

* `TauCeti.ModularForm.exists_height_nonvanishing`: a nonzero form does not vanish at
  points of imaginary part above some height.
* `TauCeti.ModularForm.finite_zeros_in_fd`: finiteness of the nonzero-order points in `𝒟`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open Complex Filter Metric Set UpperHalfPlane TauCeti.UpperHalfPlane

open scoped ModularForm MatrixGroups Modular Topology

namespace TauCeti

namespace ModularForm

variable {k : ℤ} {f : ModularForm 𝒮ℒ k}

private lemma one_mem_strictPeriods : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by simp

private lemma cuspFunction_not_eventually_zero (hf : f ≠ 0) :
    ¬∀ᶠ q in 𝓝 (0 : ℂ), cuspFunction 1 f q = 0 := by
  intro h_ev
  have h_diff : DifferentiableOn ℂ (cuspFunction 1 f) (ball 0 1) := fun q hq ↦
    (ModularFormClass.differentiableAt_cuspFunction f one_pos one_mem_strictPeriods
      (by rwa [mem_ball, dist_zero_right] at hq)).differentiableWithinAt
  have h_eqOn : EqOn (cuspFunction 1 f) 0 (ball 0 1) :=
    (h_diff.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball 0 1).isPreconnected (mem_ball_self one_pos) h_ev
  refine hf (DFunLike.coe_injective (funext fun τ ↦ ?_))
  rw [ModularForm.coe_zero, Pi.zero_apply,
    ← SlashInvariantFormClass.eq_cuspFunction f τ one_mem_strictPeriods one_ne_zero]
  exact h_eqOn (by
    rw [mem_ball, dist_zero_right]
    exact_mod_cast norm_qParam_lt_one 1 τ)

private lemma cuspFunction_eventually_ne_zero (hf : f ≠ 0) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ), cuspFunction 1 f q ≠ 0 :=
  (ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    one_mem_strictPeriods).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (cuspFunction_not_eventually_zero hf)

/-- A nonzero level-one modular form does not vanish at points of sufficiently large
imaginary part. -/
lemma exists_height_nonvanishing (hf : f ≠ 0) :
    ∃ H : ℝ, ∀ p : ℍ, H ≤ (p : ℂ).im → f p ≠ 0 := by
  obtain ⟨s, hs_prop, hs_open, hs_zero⟩ := _root_.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (cuspFunction_eventually_ne_zero hf))
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hs_open 0 hs_zero
  refine ⟨-Real.log (r / 2) / (2 * Real.pi), fun p hp hfp ↦ ?_⟩
  have h_qmem : Function.Periodic.qParam (1 : ℝ) (p : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, Function.Periodic.norm_qParam, div_one]
    have h_exp : -2 * Real.pi * (-Real.log (r / 2) / (2 * Real.pi)) = Real.log (r / 2) := by
      field_simp
    calc Real.exp (-2 * Real.pi * (p : ℂ).im)
        ≤ Real.exp (-2 * Real.pi * (-Real.log (r / 2) / (2 * Real.pi))) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith [Real.pi_pos]
      _ = r / 2 := by rw [h_exp]; exact Real.exp_log (by linarith)
      _ < r := by linarith
  refine hs_prop _ (hr_ball h_qmem) (mem_compl_singleton_iff.mpr (Complex.exp_ne_zero _)) ?_
  rw [← SlashInvariantFormClass.eq_cuspFunction f p one_mem_strictPeriods one_ne_zero] at hfp
  exact hfp

/-- The set of points of the fundamental domain at which the vanishing order of a nonzero
level-one modular form is nonzero is finite. -/
lemma finite_zeros_in_fd (hf : f ≠ 0) :
    Set.Finite {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0} := by
  obtain ⟨H₀, hH₀_no⟩ := exists_height_nonvanishing hf
  by_contra h_inf
  have h_zero : ∀ p : ℍ, orderOfVanishingAt (⇑f) p ≠ 0 → f p = 0 := fun p hp ↦ by
    by_contra hne
    exact hp (orderOfVanishingAt_eq_zero_of_ne_zero
      (analyticAt_comp_ofComplex (ModularFormClass.holo f) p.im_pos).meromorphicNFAt hne)
  have h_sub : {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0} ⊆
      ModularGroup.truncatedFundamentalDomain H₀ := fun p ⟨hp_fd, hp_ord⟩ ↦ by
    refine ⟨hp_fd, ?_⟩
    by_contra! h_gt
    exact hH₀_no p h_gt.le (h_zero p hp_ord)
  have hK : IsCompact (UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H₀) :=
    (ModularGroup.isCompact_truncatedFundamentalDomain H₀).image continuous_coe
  obtain ⟨z₀, hz₀K, hz₀_acc⟩ :=
    ((show Set.Infinite _ from h_inf).image
      UpperHalfPlane.coe_injective.injOn).exists_accPt_of_subset_isCompact hK
      (Set.image_mono h_sub |>.trans (Set.image_subset_iff.mpr fun p hp ↦ ⟨p, hp, rfl⟩))
  obtain ⟨q₀, -, rfl⟩ := hz₀K
  have h_freq : ∃ᶠ w in 𝓝[≠] (q₀ : ℂ), (⇑f ∘ ofComplex) w = 0 := by
    refine (accPt_iff_frequently_nhdsNE.mp hz₀_acc).mono ?_
    rintro w ⟨p, ⟨-, hp_ord⟩, rfl⟩
    simpa [Function.comp_apply, ofComplex_apply] using h_zero p hp_ord
  have h_analOn : AnalyticOnNhd ℂ (⇑f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    fun w hw ↦ analyticAt_comp_ofComplex (ModularFormClass.holo f) hw
  refine hf (DFunLike.coe_injective (funext fun τ ↦ ?_))
  have h_zero' := h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (Convex.isPreconnected (convex_halfSpace_im_gt 0)) q₀.im_pos h_freq τ.im_pos
  simpa [Function.comp_apply, ofComplex_apply] using h_zero'

end ModularForm

end TauCeti

end
