/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Closures and pointwise quotients

Mathlib relates `closure` to a pointwise product when one factor is *open* — `IsOpen.mul_closure`
and its neighbours in `Mathlib/Topology/Algebra/Group/Pointwise.lean`. The containment that needs
no openness hypothesis at all, and follows from continuity of division alone, is not there.

It is what a Baire argument needs. Such an argument produces a set whose *closure* has interior,
and the step from there to a neighbourhood of the identity runs through `D / D` for that closure
`D`; without this containment there is no way back from `closure s / closure t` to a closure.

## Main results

* `TauCeti.closure_div_closure_subset`, with its additive form
  `TauCeti.closure_sub_closure_subset`.
-/

public section

open Pointwise

namespace TauCeti

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- **Division carries closures into the closure of the quotient.** No openness hypothesis is
needed, unlike the `IsOpen.mul_closure` family: continuity of `(x, y) ↦ x / y` is the whole
input, applied to `closure (s ×ˢ t) = closure s ×ˢ closure t`. -/
@[to_additive /-- **Subtraction carries closures into the closure of the difference.** No openness
hypothesis is needed: continuity of `(x, y) ↦ x - y` is the whole input, applied to
`closure (s ×ˢ t) = closure s ×ˢ closure t`. -/]
theorem closure_div_closure_subset (s t : Set G) : closure s / closure t ⊆ closure (s / t) :=
  calc closure s / closure t
      = (fun p : G × G ↦ p.1 / p.2) '' (closure s ×ˢ closure t) := by
        rw [Set.image_prod, Set.image2_div]
    _ = (fun p : G × G ↦ p.1 / p.2) '' closure (s ×ˢ t) := by rw [closure_prod_eq]
    _ ⊆ closure ((fun p : G × G ↦ p.1 / p.2) '' (s ×ˢ t)) :=
        image_closure_subset_closure_image (continuous_fst.div' continuous_snd)
    _ = closure (s / t) := by rw [Set.image_prod, Set.image2_div]

end TauCeti

end
