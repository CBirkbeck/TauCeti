/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.NumberTheory.ModularForms.Order.AtCusp
public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing

import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import TauCeti.Topology.DiscreteSeparation

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
* `TauCeti.ModularForm.not_accPt_zeros_comp_ofComplex`: the extension's zeros do not
  accumulate in the upper half-plane.
* `TauCeti.ModularForm.exists_isOpen_zeros_inter`: an open neighbourhood isolating a
  subset's zeros.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open Complex Filter Metric Set UpperHalfPlane TauCeti.UpperHalfPlane

open scoped ModularForm MatrixGroups Modular Topology

namespace TauCeti

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {f : F} {h : ℝ}

/-- A nonzero modular form with a positive strict period does not vanish at points of
sufficiently large imaginary part. -/
lemma exists_height_nonvanishing [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ∃ H : ℝ, ∀ p : ℍ, H ≤ (p : ℂ).im → f p ≠ 0 := by
  have h_ev : ∀ᶠ p : ℍ in atImInfty, cuspFunction h f (Function.Periodic.qParam h ↑p) ≠ 0 :=
    ((Function.Periodic.qParam_tendsto hh).comp tendsto_coe_atImInfty).eventually
      (cuspFunction_eventually_ne_zero hh hΓ hf)
  obtain ⟨H, hH⟩ := (atImInfty_mem _).mp h_ev
  refine ⟨H, fun p hp hfp ↦ hH p (by rwa [UpperHalfPlane.coe_im] at hp) ?_⟩
  rw [← SlashInvariantFormClass.eq_cuspFunction f p hΓ hh.ne'] at hfp
  exact hfp

/-- The set of points of the fundamental domain at which the vanishing order of a nonzero
level-one modular form is nonzero is finite. -/
lemma finite_zeros_in_fd [ModularFormClass F 𝒮ℒ k] (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    Set.Finite {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0} := by
  obtain ⟨H₀, hH₀_no⟩ := exists_height_nonvanishing one_pos (by simp) hf
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
    exact hp_ord ((orderOfVanishingAt_eq_zero_iff (ModularFormClass.holo f) hf).mpr hne')
  have hpK : (p : ℂ) ∈ UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H₀ :=
    ⟨p, ⟨hp_fd, by by_contra! h_gt; exact hH₀_no p h_gt.le h_zero⟩, rfl⟩
  rw [Set.mem_preimage, Function.mem_support, ne_eq,
    MeromorphicOn.divisor_apply h_mero hpK]
  intro h0
  exact hp_ord (by rwa [orderOfVanishingAt_def])

/-- The zeros of a nonzero form's complex extension do not accumulate at any point of the
upper half-plane. -/
lemma not_accPt_zeros_comp_ofComplex [ModularFormClass F Γ k] (hf : (⇑f : ℍ → ℂ) ≠ 0)
    {x : ℂ} (hx : 0 < x.im) :
    ¬AccPt x (Filter.principal {z : ℂ | 0 < z.im ∧ (⇑f ∘ ofComplex) z = 0}) := by
  have han : AnalyticAt ℂ (⇑f ∘ ofComplex) x :=
    analyticAt_comp_ofComplex (ModularFormClass.holo f) hx
  rcases han.eventually_eq_zero_or_eventually_ne_zero with hev | hev
  · refine absurd (funext fun p => ?_) hf
    have hall : AnalyticOnNhd ℂ (⇑f ∘ ofComplex) {z : ℂ | 0 < z.im} := fun w hw =>
      analyticAt_comp_ofComplex (ModularFormClass.holo f) hw
    have h0 := hall.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_im_gt 0).isPreconnected hx hev
    have := h0 (Set.mem_ofPred_eq ▸ p.2 : (p : ℂ) ∈ {z : ℂ | 0 < z.im})
    simpa [Function.comp, ofComplex_apply] using this
  · rw [accPt_iff_frequently_nhdsNE]
    intro hfreq
    obtain ⟨y, hymem, hyne⟩ := (hfreq.and_eventually hev).exists
    exact hyne hymem.2

/-- Any subset of the upper half-plane has an open neighbourhood in the upper half-plane
containing no zeros of the form's complex extension beyond its own. -/
lemma exists_isOpen_zeros_inter [ModularFormClass F Γ k] (hf : (⇑f : ℍ → ℂ) ≠ 0)
    {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im}) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ U ⊆ {z : ℂ | 0 < z.im} ∧
      {z ∈ U | (⇑f ∘ ofComplex) z = 0} = {z ∈ K | (⇑f ∘ ofComplex) z = 0} := by
  obtain ⟨U, hUo, hKU, hUV, hUZ⟩ := TauCeti.exists_isOpen_inter_eq_of_not_accPt
    (Z := {z : ℂ | 0 < z.im ∧ (⇑f ∘ ofComplex) z = 0})
    isOpen_upperHalfPlaneSet hK fun x hx => not_accPt_zeros_comp_ofComplex hf (hK hx)
  refine ⟨U, hUo, hKU, hUV, ?_⟩
  have hmassage : ∀ {W : Set ℂ}, W ⊆ {z : ℂ | 0 < z.im} →
      {z ∈ W | (⇑f ∘ ofComplex) z = 0} =
        W ∩ {z : ℂ | 0 < z.im ∧ (⇑f ∘ ofComplex) z = 0} := by
    intro W hW
    ext z
    exact ⟨fun hz => ⟨hz.1, hW hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩
  rw [hmassage hUV, hmassage hK, hUZ]

end ModularForm

end TauCeti

end
