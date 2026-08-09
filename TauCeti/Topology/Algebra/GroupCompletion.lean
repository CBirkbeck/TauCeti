/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open subgroups in the completion of a uniform additive group

The closure in `Â` of the image of an open additive subgroup of `A` is open. Only the additive
structure is involved — no ring, no nonarchimedean hypothesis — so this extends Mathlib's
`Mathlib/Topology/Algebra/GroupCompletion.lean`, whose `toCompl` it is stated about, and lives
in the `UniformSpace.Completion` namespace of the construction it describes.

## Main results

* `UniformSpace.Completion.isOpen_closure_image_coe`: the closure in `Â` of the image of an open
  additive subgroup of `A` is open.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.32, for the completion of
  a topological group.
* The proof adapts the neighbourhood argument of `UniformSpace.Completion.isDenseInducing_coe`
  (`Mathlib/Topology/UniformSpace/Completion.lean`).
-/

public section

open UniformSpace

namespace UniformSpace.Completion

variable {A : Type*} [AddGroup A] [UniformSpace A] [IsUniformAddGroup A]

/-- The closure in the completion of the image of an open additive subgroup is open. Only the
additive structure is involved. -/
theorem isOpen_closure_image_coe {G : AddSubgroup A} (hG : IsOpen (G : Set A)) :
    IsOpen (closure (((↑) : A → Completion A) '' (G : Set A))) := by
  have hmem := Completion.isDenseInducing_coe.closure_image_mem_nhds (hG.mem_nhds G.zero_mem)
  rw [Completion.coe_zero] at hmem
  exact AddSubgroup.isOpen_of_mem_nhds ((G.map Completion.toCompl).topologicalClosure) hmem


end UniformSpace.Completion
