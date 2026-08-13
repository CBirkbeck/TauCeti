/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Discrete uniformities are complete

Two complements to Mathlib's `DiscreteUniformity`: a space with the discrete uniformity is
complete — a Cauchy filter must contain a subsingleton and hence converges to its point — and
a uniform additive group whose topology is discrete has the discrete uniformity, since its
uniformity is the comap of the (discrete) neighbourhood filter of zero.

## Main results

* `TauCeti.DiscreteUniformity.completeSpace` : a discrete uniformity is complete.
* `TauCeti.DiscreteUniformity.of_discreteTopology` : a uniform additive group with discrete
  topology has the discrete uniformity. Stated as a theorem, not an instance: together with
  Mathlib's `DiscreteUniformity → DiscreteTopology` instance it would form a resolution cycle.
-/

public section

namespace TauCeti

open Filter

/-- A space with the discrete uniformity is complete: a Cauchy filter contains an
`SetRel.id`-small set, which is a subsingleton, so the filter converges to its point. -/
instance DiscreteUniformity.completeSpace (X : Type*) [UniformSpace X] [DiscreteUniformity X] :
    CompleteSpace X where
  complete {f} hf := by
    obtain ⟨s, hsf, t, htf, hst⟩ :=
      Filter.mem_prod_iff.mp (hf.2 (DiscreteUniformity.relId_mem_uniformity X))
    obtain ⟨x, hx⟩ := (hf.1.nonempty_of_mem (Filter.inter_mem hsf htf))
    refine ⟨x, le_trans (Filter.le_pure_iff.mpr ?_) (by rw [nhds_discrete])⟩
    refine Filter.mem_of_superset (Filter.inter_mem hsf htf) fun y hy ↦ ?_
    exact (hst (Set.mk_mem_prod hx.1 hy.2) : x = y).symm

/-- A uniform additive group whose topology is discrete has the discrete uniformity: the
uniformity is the comap of the neighbourhood filter of zero under the difference map, and
`{0}` is a neighbourhood of zero.

A theorem rather than an instance: Mathlib's `DiscreteUniformity → DiscreteTopology`
instance points the other way, and registering both directions would loop. -/
theorem DiscreteUniformity.of_discreteTopology {G : Type*} [AddGroup G] [UniformSpace G]
    [IsUniformAddGroup G] [DiscreteTopology G] : DiscreteUniformity G := by
  rw [discreteUniformity_iff_setRelId_mem_uniformity, uniformity_eq_comap_nhds_zero G]
  refine Filter.mem_comap.mpr ⟨{0}, (isOpen_discrete _).mem_nhds rfl, fun p hp ↦ ?_⟩
  simpa [SetRel.id, sub_eq_zero, eq_comm] using hp

end TauCeti
