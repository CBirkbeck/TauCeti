/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants

/-!
# The group sum of a finite-group representation has the invariants as its range

Mathlib builds the averaging projection `Representation.averageMap` out of the group-algebra
element `GroupAlgebra.average`, and records that it projects onto the invariants
(`Representation.isProj_averageMap`). Neither mentions the bare group sum `∑ g, ρ g`, which is the
shape a symmetrization operator actually takes at a use site: the normalizing factor `⅟(#G)` is
usually left implicit there, and reinstating it by hand is the step that gets rewritten.

This file supplies the bridge. Unfolding the group algebra once identifies `averageMap` with the
group sum scaled by `⅟(#G)`, and since scaling by a unit changes no image, the group sum has the
same range as the projection: the invariants.

## Main results

* `Representation.averageMap_eq_invOf_card_smul_sum`: the averaging projection is the group sum
  scaled by the inverse of the group order.
* `Representation.range_sum_eq_invariants`: the group sum `∑ g, ρ g` has the invariants as its
  range.
-/

public section

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)]

/-- **The averaging projection is the normalized group sum.** Mathlib defines
`Representation.averageMap` through the group algebra; this unfolds that definition to the sum of
the operators `ρ g`, scaled by the inverse of the group order. -/
theorem averageMap_eq_invOf_card_smul_sum :
    ρ.averageMap = ⅟(Fintype.card G : k) • ∑ g : G, ρ g := by
  simp only [averageMap, GroupAlgebra.average, map_smul, map_sum, MonoidAlgebra.of_apply,
    asAlgebraHom_single_one]

/-- **The group sum has the invariants as its range.** When `#G` is invertible in `k`, the operator
`∑ g, ρ g` maps onto the invariants of `ρ`: it agrees with the averaging projection up to the unit
`#G`, so the two have the same image. -/
theorem range_sum_eq_invariants : LinearMap.range (∑ g : G, ρ g) = ρ.invariants := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨w, rfl⟩
    have hw : (∑ g : G, ρ g) w = (Fintype.card G : k) • ρ.averageMap w := by
      rw [averageMap_eq_invOf_card_smul_sum, LinearMap.smul_apply, smul_smul, mul_invOf_self,
        one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ (ρ.averageMap_invariant w)
  · refine ⟨⅟(Fintype.card G : k) • v, ?_⟩
    rw [map_smul, ← LinearMap.smul_apply, ← averageMap_eq_invOf_card_smul_sum]
    exact ρ.averageMap_id v hv

end Representation
