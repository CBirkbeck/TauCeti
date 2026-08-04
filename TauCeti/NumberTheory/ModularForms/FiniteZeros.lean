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

A nonzero level-one modular form does not vanish above some height (its cusp function is
nonvanishing on a punctured `q`-ball), and its zeros in any bounded strip are finite by
the identity theorem; consequently the set of points of the standard fundamental domain
`𝒟` at which its vanishing order is nonzero is finite — the finite-support input to the
valence formula.

## Main declarations

* `TauCeti.ModularForm.exists_height_nonvanishing`: a nonzero form does not vanish at
  points of imaginary part above some height.
* `TauCeti.ModularForm.finite_zeros_in_fd`: finiteness of the nonzero-order points in `𝒟`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open Complex Filter Metric Set UpperHalfPlane

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
    ∃ H : ℝ, Real.sqrt 3 / 2 < H ∧ ∀ p : ℍ, H ≤ (p : ℂ).im → f p ≠ 0 := by
  obtain ⟨s, hs_prop, hs_open, hs_zero⟩ := _root_.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (cuspFunction_eventually_ne_zero hf))
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hs_open 0 hs_zero
  refine ⟨max (-Real.log (r / 2) / (2 * Real.pi)) (Real.sqrt 3 / 2 + 1),
    lt_of_lt_of_le (by linarith) (le_max_right _ _), fun p hp hfp ↦ ?_⟩
  have h_qmem : Function.Periodic.qParam (1 : ℝ) (p : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, Function.Periodic.norm_qParam, div_one]
    calc Real.exp (-2 * Real.pi * (p : ℂ).im)
        ≤ Real.exp (-2 * Real.pi * (-Real.log (r / 2) / (2 * Real.pi))) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith [Real.pi_pos, le_trans (le_max_left _ _) hp]
      _ = r / 2 := by
          rw [show -2 * Real.pi * (-Real.log (r / 2) / (2 * Real.pi)) = Real.log (r / 2) by
            field_simp]
          exact Real.exp_log (by linarith)
      _ < r := by linarith
  refine hs_prop _ (hr_ball h_qmem) (mem_compl_singleton_iff.mpr (Complex.exp_ne_zero _)) ?_
  rw [← SlashInvariantFormClass.eq_cuspFunction f p one_mem_strictPeriods one_ne_zero] at hfp
  exact hfp

private lemma finite_zeros_in_strip (hf : f ≠ 0) {M : ℝ} (hM : (1 : ℝ) / 2 < M) :
    Set.Finite {z : ℂ | (-1 < z.re ∧ z.re < 1 ∧ (1 : ℝ) / 2 < z.im ∧ z.im < M) ∧
      (⇑f ∘ ofComplex) z = 0} := by
  by_contra h_inf
  have hBdd : Bornology.IsBounded
      {z : ℂ | -1 < z.re ∧ z.re < 1 ∧ (1 : ℝ) / 2 < z.im ∧ z.im < M} :=
    isBounded_iff_forall_norm_le.mpr ⟨1 + M, fun z hz ↦
      (Complex.norm_le_abs_re_add_abs_im z).trans (by
        have h1 : |z.re| < 1 := abs_lt.mpr ⟨by linarith [hz.1], hz.2.1⟩
        have h2 : |z.im| ≤ M := abs_le.mpr ⟨by linarith [hz.2.2.1], hz.2.2.2.le⟩
        linarith)⟩
  obtain ⟨z₀, hz₀K, hz₀_acc⟩ :=
    (show Set.Infinite _ from h_inf).exists_accPt_of_subset_isCompact
      hBdd.isCompact_closure (fun z hz ↦ subset_closure hz.1)
  have hz₀_pos : 0 < z₀.im := by
    have h_half : (1 : ℝ) / 2 ≤ z₀.im := closure_minimal (fun z hz ↦ hz.2.2.1.le)
      (isClosed_le continuous_const Complex.continuous_im) hz₀K
    linarith
  have h_freq : ∃ᶠ y in 𝓝[≠] z₀, (⇑f ∘ ofComplex) y = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hz₀_acc).mono fun y hy ↦ hy.2
  have h_analOn : AnalyticOnNhd ℂ (⇑f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    fun w hw ↦ analyticAt_comp_ofComplex (ModularFormClass.holo f) hw
  refine hf (DFunLike.coe_injective (funext fun τ ↦ ?_))
  have h_zero := h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (Convex.isPreconnected (convex_halfSpace_im_gt 0)) hz₀_pos h_freq τ.im_pos
  simpa [Function.comp_apply, ofComplex_apply] using h_zero

/-- A point of the standard fundamental domain has imaginary part above `1/2`. -/
lemma fd_im_gt_half {p : ℍ} (hp : p ∈ 𝒟) : (1 : ℝ) / 2 < (p : ℂ).im := by
  by_contra! h_le
  obtain ⟨hnormSq, habs_re⟩ := hp
  have hre := abs_le.mp habs_re
  nlinarith [normSq_apply (p : ℂ), p.im_pos, mul_self_nonneg (p : ℂ).re,
    show UpperHalfPlane.re p = (p : ℂ).re from rfl, show p.im = (p : ℂ).im from rfl]

/-- The set of points of the fundamental domain at which the vanishing order of a nonzero
level-one modular form is nonzero is finite. -/
lemma finite_zeros_in_fd (hf : f ≠ 0) :
    Set.Finite {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0} := by
  obtain ⟨H₀, hH₀_gt, hH₀_no⟩ := exists_height_nonvanishing hf
  have hM : (1 : ℝ) / 2 < H₀ + 1 := by nlinarith [Real.sqrt_nonneg 3]
  refine ((finite_zeros_in_strip hf hM).preimage
    ((UpperHalfPlane.coe_injective).injOn)).subset fun p ⟨hp_fd, hp_ord⟩ ↦ ?_
  have hfp : f p = 0 := by
    by_contra hne
    exact hp_ord (orderOfVanishingAt_eq_zero_of_ne_zero
      (analyticAt_comp_ofComplex (ModularFormClass.holo f) p.im_pos).meromorphicNFAt hne)
  have hre := abs_le.mp hp_fd.2
  have him_lt : (p : ℂ).im < H₀ + 1 := by
    by_contra! h_ge
    exact hH₀_no p (by linarith) hfp
  refine ⟨⟨?_, ?_, fd_im_gt_half hp_fd, him_lt⟩, ?_⟩
  · have : UpperHalfPlane.re p = (p : ℂ).re := rfl
    linarith [hre.1]
  · have : UpperHalfPlane.re p = (p : ℂ).re := rfl
    linarith [hre.2]
  · simpa [Function.comp_apply, ofComplex_apply] using hfp

end ModularForm

end TauCeti

end
