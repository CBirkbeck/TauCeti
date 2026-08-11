/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Separation.Regular

/-!
# Closures of images under a map continuous at a point

An approximation argument that controls its errors only up to closure — as Henkel's open mapping
theorem does — tracks a point through the sets `closure (f '' V)` rather than through `f '' V`.
It converges only if those closures become small as `V` does, and continuity by itself says
nothing about them: it bounds `f '' V`, not the closure.

Regularity of the target supplies what is missing. A neighbourhood of `f x` contains a *closed*
neighbourhood; a closed set contains the closure of every image it contains; and continuity at
`x` produces a neighbourhood whose image lands inside it.

## Main results

* `ContinuousAt.exists_mem_nhds_closure_image_subset`: over a regular target, every neighbourhood
  of `f x` contains `closure (f '' V)` for some neighbourhood `V` of `x`.

Mathlib's `Filter.HasBasis.hasBasis_of_isDenseInducing` (Bourbaki, *General Topology* III §3
no. 4, Proposition 7) draws a stronger conclusion from a stronger hypothesis: for a dense
inducing map, the closures of the images of a basis at `x` are themselves a basis at `f x`. The
containment above is what survives when `f` is merely continuous at `x`.
-/

public section

open Filter Set Topology

namespace ContinuousAt

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [RegularSpace Y]

/-- If `f` is continuous at `x` and the target is regular, then every neighbourhood `W` of `f x`
contains `closure (f '' V)` for some neighbourhood `V` of `x`. -/
theorem exists_mem_nhds_closure_image_subset {f : X → Y} {x : X} (hf : ContinuousAt f x)
    {W : Set Y} (hW : W ∈ 𝓝 (f x)) : ∃ V ∈ 𝓝 x, closure (f '' V) ⊆ W := by
  obtain ⟨W', hW'mem, hW'closed, hW'sub⟩ := exists_mem_nhds_isClosed_subset hW
  exact ⟨f ⁻¹' W', hf hW'mem,
    (closure_minimal (image_preimage_subset _ _) hW'closed).trans hW'sub⟩

end ContinuousAt

end
