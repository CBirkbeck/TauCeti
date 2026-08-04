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

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {f : ModularForm Γ k} {h : ℝ}

private lemma cuspFunction_not_eventually_zero (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hf : f ≠ 0) : ¬∀ᶠ q in 𝓝 (0 : ℂ), cuspFunction h f q = 0 := by
  intro h_ev
  have h_diff : DifferentiableOn ℂ (cuspFunction h f) (ball 0 1) := fun q hq ↦
    (ModularFormClass.differentiableAt_cuspFunction f hh hΓ
      (by rwa [mem_ball, dist_zero_right] at hq)).differentiableWithinAt
  have h_eqOn : EqOn (cuspFunction h f) 0 (ball 0 1) :=
    (h_diff.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball 0 1).isPreconnected (mem_ball_self one_pos) h_ev
  refine hf (DFunLike.coe_injective (funext fun τ ↦ ?_))
  rw [ModularForm.coe_zero, Pi.zero_apply,
    ← SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne']
  exact h_eqOn (by
    rw [mem_ball, dist_zero_right]
    exact_mod_cast Function.Periodic.norm_qParam_lt_one hh τ.im_pos)

private lemma cuspFunction_eventually_ne_zero (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hf : f ≠ 0) : ∀ᶠ q in 𝓝[≠] (0 : ℂ), cuspFunction h f q ≠ 0 :=
  (ModularFormClass.analyticAt_cuspFunction_zero f hh
    hΓ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (cuspFunction_not_eventually_zero hh hΓ hf)

/-- A nonzero modular form with a positive strict period does not vanish at points of
sufficiently large imaginary part. -/
lemma exists_height_nonvanishing (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (hf : f ≠ 0) :
    ∃ H : ℝ, ∀ p : ℍ, H ≤ (p : ℂ).im → f p ≠ 0 := by
  obtain ⟨s, hs_prop, hs_open, hs_zero⟩ := _root_.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (cuspFunction_eventually_ne_zero hh hΓ hf))
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hs_open 0 hs_zero
  refine ⟨-h * Real.log (r / 2) / (2 * Real.pi), fun p hp hfp ↦ ?_⟩
  have h_qmem : Function.Periodic.qParam h (p : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, Function.Periodic.norm_qParam]
    have h_exp : -2 * Real.pi * ((-h * Real.log (r / 2) / (2 * Real.pi)) / h) =
        Real.log (r / 2) := by
      field_simp
    calc Real.exp (-2 * Real.pi * (p : ℂ).im / h)
        ≤ Real.exp (-2 * Real.pi * ((-h * Real.log (r / 2) / (2 * Real.pi)) / h)) := by
          refine Real.exp_le_exp.mpr ?_
          rw [← mul_div_assoc]
          refine (div_le_div_iff_of_pos_right hh).mpr ?_
          have := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
          linarith
      _ = r / 2 := by rw [h_exp]; exact Real.exp_log (by linarith)
      _ < r := by linarith
  refine hs_prop _ (hr_ball h_qmem) (mem_compl_singleton_iff.mpr (Complex.exp_ne_zero _)) ?_
  rw [← SlashInvariantFormClass.eq_cuspFunction f p hΓ hh.ne'] at hfp
  exact hfp

/-- The set of points of the fundamental domain at which the vanishing order of a nonzero
level-one modular form is nonzero is finite. -/
lemma finite_zeros_in_fd {f : ModularForm 𝒮ℒ k} (hf : f ≠ 0) :
    Set.Finite {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0} := by
  obtain ⟨H₀, hH₀_no⟩ := exists_height_nonvanishing one_pos (by simp) hf
  have hne : (⇑f : ℍ → ℂ) ≠ 0 := (ModularForm.coe_eq_zero_iff f).not.mpr hf
  have hK : IsCompact (UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H₀) :=
    (ModularGroup.isCompact_truncatedFundamentalDomain H₀).image continuous_coe
  have hK_im : ∀ z ∈ UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H₀,
      0 < z.im := by
    rintro _ ⟨q, -, rfl⟩
    exact q.im_pos
  have h_mero : MeromorphicOn (⇑f ∘ ofComplex)
      (UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H₀) := fun z hz ↦
    (analyticAt_comp_ofComplex (ModularFormClass.holo f) (hK_im z hz)).meromorphicAt
  have h_fin := MeromorphicOn.divisor_support_finite_of_subset h_mero hK subset_rfl
  refine (h_fin.preimage UpperHalfPlane.coe_injective.injOn).subset ?_
  rintro p ⟨hp_fd, hp_ord⟩
  have h_zero : f p = 0 := by
    by_contra hne'
    exact hp_ord ((orderOfVanishingAt_eq_zero_iff (ModularFormClass.holo f) hne).mpr hne')
  have hpK : (p : ℂ) ∈ UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H₀ :=
    ⟨p, ⟨hp_fd, by by_contra! h_gt; exact hH₀_no p h_gt.le h_zero⟩, rfl⟩
  rw [Set.mem_preimage, Function.mem_support, ne_eq,
    MeromorphicOn.divisor_apply h_mero hpK]
  intro h0
  exact hp_ord (by rwa [orderOfVanishingAt_def])

end ModularForm

end TauCeti

end
