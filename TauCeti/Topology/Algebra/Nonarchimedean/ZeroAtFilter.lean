/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Cofinite convergence in a nonarchimedean group is a finiteness condition

In a nonarchimedean additive group the open subgroups form a basis of neighbourhoods of zero, so
a family converges to zero along the cofinite filter exactly when each open subgroup omits only
finitely many of its members.

The `→` direction is available in any topological additive group: an open subgroup is a
neighbourhood of zero, so cofinitely many members lie in it. It is nonarchimedeanness that gives
the converse, and with it the upgrade from a *consequence* of convergence to a *criterion* for it.

Nothing here looks at the index type, so it is arbitrary.

## Main results

* `NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem`
-/

public section

open Filter Topology

namespace NonarchimedeanAddGroup

variable {ι : Type*} {G : Type*} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]

/-- **Cofinite convergence, as a finiteness condition on open subgroups.** A family tends to `0`
along the cofinite filter exactly when, for every open additive subgroup `W`, all but finitely
many of its members lie in `W`.

The `→` direction needs only that an open subgroup is a neighbourhood of zero. The `←` direction
is where nonarchimedeanness is used: it supplies an open subgroup inside each neighbourhood of
zero, so the open subgroups are a neighbourhood basis and the finiteness condition is enough. -/
theorem zeroAtFilter_cofinite_iff_finite_notMem {f : ι → G} :
    ZeroAtFilter cofinite f ↔ ∀ W : OpenAddSubgroup G, {n | f n ∉ (W : Set G)}.Finite := by
  refine ⟨fun hf W ↦ ?_, fun h ↦ ?_⟩
  · have := (tendsto_nhds.mp hf) _ W.isOpen (SetLike.mem_coe.mpr W.zero_mem)
    rwa [Filter.mem_cofinite] at this
  · refine tendsto_nhds.mpr fun U hU h0 ↦ ?_
    obtain ⟨W, hWU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U (hU.mem_nhds h0)
    rw [Filter.mem_cofinite]
    exact (h W).subset fun n hn ↦ fun hnW ↦ hn (hWU hnW)

end NonarchimedeanAddGroup
