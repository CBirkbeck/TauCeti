/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.NumberTheory.ModularForms.Order.AtCusp
public import TauCeti.NumberTheory.ModularForms.Norm.Order
public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing


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
* `TauCeti.ModularForm.finite_zeros_in_fd_of_isFiniteRelIndex`: the same at any level of
  finite relative index, obtained from the level-one statement through the norm.

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

/-- A nonzero modular form on a subgroup of finite relative index in `𝒮ℒ` has only finitely
many zeros in the standard fundamental domain.

The norm of `f` is a level-one form, so `finite_zeros_in_fd` applies to it, and `f` vanishes
to no greater order than its norm does — so the zero set of `f` sits inside a finite one. -/
lemma finite_zeros_in_fd_of_isFiniteRelIndex {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [𝒢.IsFiniteRelIndex 𝒮ℒ] [ModularFormClass F 𝒢 k] (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    Set.Finite {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0} := by
  -- `norm_ne_zero` states the bundled form is nonzero; `finite_zeros_in_fd` needs the coercion.
  have hN : (⇑(_root_.ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) ≠ 0 := fun h =>
    _root_.ModularForm.norm_ne_zero 𝒮ℒ hf (DFunLike.coe_injective (by simpa using h))
  refine (finite_zeros_in_fd hN).subset fun p ⟨hp, hord⟩ ↦ ⟨hp, ?_⟩
  -- A nonzero order is positive and is dominated by the norm's, so the norm's is nonzero too.
  have h0 : 0 ≤ orderOfVanishingAt (⇑f) p :=
    orderOfVanishingAt_nonneg (ModularFormClass.holo f) p
  have hle := orderOfVanishingAt_le_orderOfVanishingAt_norm (ℋ := 𝒮ℒ) f hf p
  omega

end ModularForm

end TauCeti

end
