/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Separation.Basic

import Mathlib.Topology.Compactness.Compact

/-!
# Shrinking an open set to isolate the compact part of a discrete set

A set that is closed and discrete inside an open ambient set meets a compact subset in
finitely many points, and the ambient set shrinks to an open neighbourhood of the compact
subset meeting the discrete set in exactly those points. This is the standard localization
step for residue computations: a contour region is shrunk until the only singularities it
contains are the finitely many inside the contour's compact hull.

## Main declarations

* `TauCeti.exists_isOpen_inter_eq_of_not_accPt`.
-/

public section

namespace TauCeti

/-- A set `K ⊆ V` at whose points `Z` does not accumulate shrinks the open ambient `V` to
an open neighbourhood meeting `Z` exactly in `K ∩ Z`: remove the closure of the rest of
`Z`. -/
theorem exists_isOpen_inter_eq_of_not_accPt {X : Type*} [TopologicalSpace X] {V Z K : Set X}
    (hV : IsOpen V) (hKV : K ⊆ V) (hacc : ∀ x ∈ K, ¬AccPt x (Filter.principal Z)) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ U ⊆ V ∧ U ∩ Z = K ∩ Z := by
  have hKU : K ⊆ V \ closure (Z \ K) := by
    intro x hx
    refine ⟨hKV hx, fun hxc => ?_⟩
    have hx_notin : x ∉ Z \ K := fun h => h.2 hx
    have hcl : ClusterPt x (Filter.principal ((Z \ K) \ {x})) := by
      rwa [Set.sdiff_singleton_eq_self hx_notin, ← mem_closure_iff_clusterPt]
    exact hacc x hx ((accPt_principal_iff_clusterPt.mpr hcl).mono
      (Filter.principal_mono.mpr Set.sdiff_subset))
  refine ⟨V \ closure (Z \ K), hV.sdiff isClosed_closure, hKU, Set.sdiff_subset, ?_⟩
  refine Set.Subset.antisymm ?_ fun z hz => ⟨hKU hz.1, hz.2⟩
  rintro z ⟨⟨hzV, hznc⟩, hzZ⟩
  refine ⟨?_, hzZ⟩
  by_contra hzK
  exact hznc (subset_closure ⟨hzZ, hzK⟩)

end TauCeti

end
