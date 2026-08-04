/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The vanishing order of a modular form

`TauCeti.orderOfVanishingAt f z` is the order of vanishing of `f : ℍ → ℂ` at `z ∈ ℍ`, read
as the meromorphic order of `f ∘ ofComplex` at `z`; `TauCeti.orderAtCusp` is the order at
the cusp `∞` of a level-one form, read in its `q`-expansion. For a holomorphic modular
form the interior order is detected by vanishing (`orderOfVanishingAt_eq_zero_iff` under
nonvanishing of the form), and it is constant along the group action
(`orderOfVanishingAt_smul`) — the order dictionary feeding the valence formula.

## Main declarations

* `TauCeti.orderOfVanishingAt`, `TauCeti.orderAtCusp`.
* `TauCeti.orderOfVanishingAt_smul`: invariance along the action of the group.
* `TauCeti.orderOfVanishingAt_ne_zero_of_eq_zero`: a zero of a nonzero form has
  nonzero order.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex

open scoped ModularForm MatrixGroups

namespace TauCeti

/-- The order of vanishing of `f : ℍ → ℂ` at `z ∈ ℍ`: the meromorphic order of
`f ∘ ofComplex` at `z`, with the conventions that a function vanishing in a neighborhood
of `z` (in particular the zero function) and a function not meromorphic at `z` both get
order `0`. -/
def orderOfVanishingAt (f : ℍ → ℂ) (z : ℍ) : ℤ :=
  (meromorphicOrderAt (f ∘ ofComplex) (z : ℂ)).untop₀

/-- The order of vanishing at the cusp `∞` of a level-one modular form, read in its
`q`-expansion, with the convention that the zero form gets order `0`. -/
def orderAtCusp {k : ℤ} (f : ModularForm 𝒮ℒ k) : ℤ :=
  (qExpansion 1 f).order.toNat

variable {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]

private lemma analyticAt_comp_ofComplex [ModularFormClass F Γ k] (f : F) {w : ℂ}
    (hw : 0 < w.im) : AnalyticAt ℂ (⇑f ∘ ofComplex) w :=
  (UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds hw)

/-- At a point where a holomorphic modular form does not vanish, its order is zero. -/
lemma orderOfVanishingAt_eq_zero_of_ne_zero [ModularFormClass F Γ k] (f : F) {z : ℍ}
    (hz : f z ≠ 0) : orderOfVanishingAt f z = 0 := by
  have h_nf : MeromorphicNFAt (⇑f ∘ ofComplex) (z : ℂ) :=
    (analyticAt_comp_ofComplex f z.im_pos).meromorphicNFAt
  have : (⇑f ∘ ofComplex) (z : ℂ) ≠ 0 := by
    simpa [Function.comp_apply, ofComplex_apply] using hz
  rw [orderOfVanishingAt, h_nf.meromorphicOrderAt_eq_zero_iff.mpr this]
  rfl

/-- A nonzero holomorphic modular form has finite vanishing order at every point of `ℍ`. -/
lemma meromorphicOrderAt_comp_ofComplex_ne_top [ModularFormClass F Γ k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (z : ℍ) : meromorphicOrderAt (⇑f ∘ ofComplex) (z : ℂ) ≠ ⊤ := by
  intro htop
  refine hf (funext fun τ ↦ ?_)
  have h_eqOn : Set.EqOn (⇑f ∘ ofComplex) 0 upperHalfPlaneSet := by
    have h_top : analyticOrderAt (⇑f ∘ ofComplex) (z : ℂ) = ⊤ := by
      have := (analyticAt_comp_ofComplex f z.im_pos).meromorphicOrderAt_eq
      rw [htop] at this
      simpa using this.symm
    exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun w hw ↦ analyticAt_comp_ofComplex f hw)
      (Convex.isPreconnected (convex_halfSpace_im_gt 0)) z.im_pos
      (analyticOrderAt_eq_top.mp h_top)
  simpa [Function.comp_apply, ofComplex_apply] using h_eqOn (τ.im_pos : (τ : ℂ) ∈ _)

/-- A zero of a nonzero holomorphic modular form has nonzero vanishing order. -/
lemma orderOfVanishingAt_ne_zero_of_eq_zero [ModularFormClass F Γ k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) {z : ℍ} (hz : f z = 0) : orderOfVanishingAt f z ≠ 0 := by
  have h_nf : MeromorphicNFAt (⇑f ∘ ofComplex) (z : ℂ) :=
    (analyticAt_comp_ofComplex f z.im_pos).meromorphicNFAt
  have h_ne : meromorphicOrderAt (⇑f ∘ ofComplex) (z : ℂ) ≠ 0 := fun h0 ↦
    h_nf.meromorphicOrderAt_eq_zero_iff.mp h0 (by simp [ofComplex_apply, hz])
  rw [orderOfVanishingAt]
  exact fun h ↦ h_ne (((WithTop.untop₀_eq_zero).mp h).resolve_right
    (meromorphicOrderAt_comp_ofComplex_ne_top hf z))

/-- The vanishing order of a slash-invariant form is constant along the group action. -/
lemma orderOfVanishingAt_smul [Γ.HasDetOne] [SlashInvariantFormClass F Γ k] (f : F) {γ}
    (hγ : γ ∈ Γ) (z : ℍ) : orderOfVanishingAt f (γ • z) = orderOfVanishingAt f z := by
  have hdet : 0 < γ.val.det := by
    simp [← Matrix.GeneralLinearGroup.val_det_apply, Subgroup.HasDetOne.det_eq hγ]
  have hcongr : (fun w : ℂ ↦ f (γ • ofComplex w)) =ᶠ[nhds (z : ℂ)]
      (fun w : ℂ ↦ ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) ^ k) * (⇑f ∘ ofComplex) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    rw [Pi.mul_apply, Function.comp_apply, ofComplex_apply_of_im_pos hw]
    simpa using SlashInvariantForm.slash_action_eqn' f hγ ⟨w, hw⟩
  have h_an : AnalyticAt ℂ (fun w : ℂ ↦ ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) ^ k) (z : ℂ) := by
    refine AnalyticAt.zpow (by fun_prop) ?_
    simpa [denom] using denom_ne_zero γ z
  have h_ne : ((γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)) ^ k ≠ 0 :=
    zpow_ne_zero _ (by simpa [denom] using denom_ne_zero γ z)
  unfold orderOfVanishingAt
  conv_lhs => rw [Function.comp_def]
  rw [← meromorphicOrderAt_comp_smul hdet,
    meromorphicOrderAt_congr (hcongr.filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_mul_of_ne_zero h_an h_ne]

end TauCeti

end
