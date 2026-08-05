/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

import TauCeti.Topology.DiscreteSeparation

/-!
# Analyticity through `ofComplex`

A function holomorphic on the upper half-plane, extended to `ℂ` by `ofComplex`, is
analytic at every point of the open upper half-plane.

## Main declarations

* `TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex`.
* `TauCeti.UpperHalfPlane.not_accPt_zeros_comp_ofComplex` and
  `TauCeti.UpperHalfPlane.exists_isOpen_zeros_inter` — a subset's zeros isolate in an
  open neighbourhood.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public section

open UpperHalfPlane

open scoped Manifold

namespace TauCeti.UpperHalfPlane

/-- A function holomorphic on `ℍ` composes with `ofComplex` to a function analytic at
every point of the open upper half-plane. -/
lemma analyticAt_comp_ofComplex {f : ℍ → ℂ} (hf : MDiff f) {w : ℂ} (hw : 0 < w.im) :
    AnalyticAt ℂ (f ∘ ofComplex) w :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds hw)

/-- The zeros of a nonzero holomorphic function's complex extension do not accumulate at
any point of the upper half-plane. -/
lemma not_accPt_zeros_comp_ofComplex {g : ℍ → ℂ} (hg : MDiff g) (hg0 : g ≠ 0)
    {x : ℂ} (hx : 0 < x.im) :
    ¬AccPt x (Filter.principal {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0}) := by
  intro hacc
  rw [accPt_iff_nhds] at hacc
  refine hg0 (UpperHalfPlane.eq_zero_of_frequently hg (τ := ⟨x, hx⟩) ?_)
  rw [Filter.frequently_iff]
  intro V hV
  obtain ⟨O, hO_open, hτO, hOV⟩ := mem_nhdsWithin.mp hV
  obtain ⟨y, ⟨hyO, hyim, hyzero⟩, hyne⟩ :=
    hacc _ ((UpperHalfPlane.isOpenEmbedding_coe.isOpenMap O hO_open).mem_nhds
      (Set.mem_image_of_mem _ hτO))
  obtain ⟨τ', hτ'O, rfl⟩ := hyO
  refine ⟨τ', hOV ⟨hτ'O, fun hmem => hyne (congrArg UpperHalfPlane.coe hmem)⟩, ?_⟩
  simpa [Function.comp, ofComplex_apply] using hyzero

/-- Any subset of the upper half-plane has an open neighbourhood in the upper half-plane
containing no zeros of the function's complex extension beyond its own. -/
lemma exists_isOpen_zeros_inter {g : ℍ → ℂ} (hg : MDiff g) (hg0 : g ≠ 0)
    {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im}) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ U ⊆ {z : ℂ | 0 < z.im} ∧
      {z ∈ U | (g ∘ ofComplex) z = 0} = {z ∈ K | (g ∘ ofComplex) z = 0} := by
  have hnc : ∀ x ∈ K, x ∉ closure ({z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0} \ K) := by
    intro x hx hxc
    have hx_notin : x ∉ {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0} \ K := fun h => h.2 hx
    have hcl : ClusterPt x (Filter.principal
        (({z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0} \ K) \ {x})) := by
      rwa [Set.sdiff_singleton_eq_self hx_notin, ← mem_closure_iff_clusterPt]
    exact not_accPt_zeros_comp_ofComplex hg hg0 (hK hx)
      ((accPt_principal_iff_clusterPt.mpr hcl).mono
        (Filter.principal_mono.mpr Set.sdiff_subset))
  obtain ⟨U, hUo, hKU, hUV, hUZ⟩ := TauCeti.exists_isOpen_inter_eq_of_notMem_closure
    (Z := {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0}) isOpen_upperHalfPlaneSet hK hnc
  refine ⟨U, hUo, hKU, hUV, ?_⟩
  have hmassage : ∀ {W : Set ℂ}, W ⊆ {z : ℂ | 0 < z.im} →
      {z ∈ W | (g ∘ ofComplex) z = 0} =
        W ∩ {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0} := by
    intro W hW
    ext z
    exact ⟨fun hz => ⟨hz.1, hW hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩
  rw [hmassage hUV, hmassage hK, hUZ]

end TauCeti.UpperHalfPlane

end
