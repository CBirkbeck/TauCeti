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
the cusp `∞` with respect to a width parameter, read in the `q`-expansion. For a nonzero
holomorphic function the interior order detects vanishing
(`orderOfVanishingAt_eq_zero_iff`), and for a slash-invariant form it is constant along
the group action (`orderOfVanishingAt_smul`) — the order dictionary feeding the valence
formula.

## Main declarations

* `TauCeti.orderOfVanishingAt`, `TauCeti.orderAtCusp`.
* `TauCeti.orderOfVanishingAt_eq_zero_iff`: for a nonzero holomorphic function, the order
  at `z` vanishes exactly when the function does not vanish at `z`.
* `TauCeti.orderOfVanishingAt_smul`: invariance along the action of the group.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex

open scoped ModularForm MatrixGroups Manifold

namespace TauCeti

/-- The order of vanishing of `f : ℍ → ℂ` at `z ∈ ℍ`: the meromorphic order of
`f ∘ ofComplex` at `z`, with the conventions that a function vanishing in a neighborhood
of `z` (in particular the zero function) and a function not meromorphic at `z` both get
order `0`. -/
def orderOfVanishingAt (f : ℍ → ℂ) (z : ℍ) : ℤ :=
  (meromorphicOrderAt (f ∘ ofComplex) (z : ℂ)).untop₀

/-- The order of vanishing of `f : ℍ → ℂ` at the cusp `∞` with respect to the width
parameter `h`, read in the `q`-expansion, with the convention that the zero function gets
order `0`. -/
def orderAtCusp (h : ℝ) (f : ℍ → ℂ) : ℤ :=
  (qExpansion h f).order.toNat

/-- Restatement of `orderAtCusp` through the `q`-expansion order. -/
lemma orderAtCusp_eq (h : ℝ) (f : ℍ → ℂ) :
    orderAtCusp h f = (qExpansion h f).order.toNat := by
  unfold orderAtCusp
  rfl

variable {f : ℍ → ℂ}

private lemma analyticAt_comp_ofComplex (hf : MDiff f) {w : ℂ} (hw : 0 < w.im) :
    AnalyticAt ℂ (f ∘ ofComplex) w :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds hw)

/-- At a point where a holomorphic function on `ℍ` does not vanish, its order is zero. -/
lemma orderOfVanishingAt_eq_zero_of_ne_zero (hf : MDiff f) {z : ℍ} (hz : f z ≠ 0) :
    orderOfVanishingAt f z = 0 := by
  have h_nf : MeromorphicNFAt (f ∘ ofComplex) (z : ℂ) :=
    (analyticAt_comp_ofComplex hf z.im_pos).meromorphicNFAt
  have : (f ∘ ofComplex) (z : ℂ) ≠ 0 := by
    simpa [Function.comp_apply, ofComplex_apply] using hz
  rw [orderOfVanishingAt, h_nf.meromorphicOrderAt_eq_zero_iff.mpr this]
  rfl

private lemma meromorphicOrderAt_comp_ofComplex_ne_top (hf : MDiff f) (hne : f ≠ 0)
    (z : ℍ) : meromorphicOrderAt (f ∘ ofComplex) (z : ℂ) ≠ ⊤ := by
  obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hne
  refine MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun w hw ↦ (analyticAt_comp_ofComplex hf hw).meromorphicAt)
    (Convex.isPreconnected (convex_halfSpace_im_gt 0)) τ.im_pos z.im_pos ?_
  rw [((analyticAt_comp_ofComplex hf τ.im_pos).meromorphicNFAt).meromorphicOrderAt_eq_zero_iff.mpr
    (by simpa [Function.comp_apply, ofComplex_apply] using hτ)]
  exact WithTop.zero_ne_top

/-- A zero of a nonzero holomorphic function on `ℍ` has nonzero vanishing order. -/
lemma orderOfVanishingAt_ne_zero_of_eq_zero (hf : MDiff f) (hne : f ≠ 0) {z : ℍ}
    (hz : f z = 0) : orderOfVanishingAt f z ≠ 0 := by
  have h_nf : MeromorphicNFAt (f ∘ ofComplex) (z : ℂ) :=
    (analyticAt_comp_ofComplex hf z.im_pos).meromorphicNFAt
  have h_ne : meromorphicOrderAt (f ∘ ofComplex) (z : ℂ) ≠ 0 := fun h0 ↦
    h_nf.meromorphicOrderAt_eq_zero_iff.mp h0 (by simp [ofComplex_apply, hz])
  rw [orderOfVanishingAt]
  exact fun h ↦ h_ne (((WithTop.untop₀_eq_zero).mp h).resolve_right
    (meromorphicOrderAt_comp_ofComplex_ne_top hf hne z))

/-- For a nonzero holomorphic function on `ℍ`, the vanishing order at `z` is zero exactly
when the function does not vanish at `z`. -/
lemma orderOfVanishingAt_eq_zero_iff (hf : MDiff f) (hne : f ≠ 0) {z : ℍ} :
    orderOfVanishingAt f z = 0 ↔ f z ≠ 0 :=
  ⟨fun h hz ↦ orderOfVanishingAt_ne_zero_of_eq_zero hf hne hz h,
    orderOfVanishingAt_eq_zero_of_ne_zero hf⟩

variable {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]

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
