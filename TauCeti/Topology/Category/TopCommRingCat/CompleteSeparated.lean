/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Topology.Category.TopCommRingCat.Limits
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Topology.UniformSpace.Pi

/-!
# The category of complete separated topological commutative rings

Wedhorn's structure presheaves take values among *complete separated* topological rings
(*Adic Spaces*, arXiv:1910.05934v1, §8.1; roadmap Layer 3.2). This file defines the
predicate and the full subcategory of `TopCommRingCat` it cuts out.

A bare topological ring carries no uniformity, so completeness is stated for the canonical
group uniformity `IsTopologicalAddGroup.rightUniformSpace` of the additive topological
group. Nothing is lost against any other compatible choice:
`IsUniformAddGroup.rightUniformSpace_eq` says every uniformity making the ring a uniform
additive group with this topology *equals* the canonical one. Separatedness is stated as
`T0Space`, not `T2Space`: for a topological additive group the two are equivalent, and `T0`
is the hypothesis Mathlib's completion machinery consumes, so stating the stronger-looking
`T2` would only force callers holding `T0` to upgrade by hand.

## Main definitions

* `TauCeti.TopCommRingCat.IsCompleteSeparated`: complete and Hausdorff for the group
  uniformity of the topology.
* `TauCeti.CompleteSeparatedTopCommRingCat`: the full subcategory of `TopCommRingCat` on
  the complete separated objects.

## Main results

* `TauCeti.TopCommRingCat.IsCompleteSeparated.pi`: a product of complete separated objects
  is complete separated — the apex of `TauCeti.TopCommRingCat.piFan` stays in the
  subcategory, the first half of the roadmap's "the forgetful functor creates products and
  equalizers" for Layer 3.2.
-/

public section

universe v u

open CategoryTheory

namespace TauCeti.TopCommRingCat

/-- A topological commutative ring is **complete separated** when it is complete and
Hausdorff for the group uniformity `IsTopologicalAddGroup.rightUniformSpace` of its
topology. This is Wedhorn's standing convention that "complete" includes "Hausdorff"
(*Adic Spaces*, §5.3), separatedness stated as `T0Space` — equivalent to `T2Space` for a
topological additive group. -/
structure IsCompleteSeparated (R : TopCommRingCat.{u}) : Prop where
  /-- Completeness for the group uniformity of the topology. -/
  completeSpace :
    letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
    CompleteSpace R
  /-- Separatedness; `T0Space` suffices, and is equivalent to `T2Space` here. -/
  t0Space : T0Space R

/-- **A product of complete separated topological rings is complete separated.** The group
uniformity of the product topology is the product of the group uniformities — both make the
product a uniform additive group over the same topology, so they are equal by
`IsUniformAddGroup.rightUniformSpace_eq` — and a product of complete (respectively `T0`)
uniform spaces is complete (respectively `T0`). -/
theorem IsCompleteSeparated.pi {β : Type v} {f : β → TopCommRingCat.{max u v}}
    (hf : ∀ b, IsCompleteSeparated (f b)) :
    IsCompleteSeparated (TopCommRingCat.of (∀ b, f b)) := by
  let _ : ∀ b, UniformSpace (f b) := fun b ↦ IsTopologicalAddGroup.rightUniformSpace _
  have huag : ∀ b, IsUniformAddGroup (f b) := fun b ↦ isUniformAddGroup_of_addCommGroup
  have hcompl : ∀ b, CompleteSpace (f b) := fun b ↦ (hf b).completeSpace
  have ht0 : ∀ b, T0Space (f b) := fun b ↦ (hf b).t0Space
  refine ⟨?_, inferInstance⟩
  let _ : UniformSpace (∀ b, f b) := Pi.uniformSpace _
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

end TauCeti.TopCommRingCat

namespace TauCeti

/-- The category of complete separated topological commutative rings: the full subcategory
of `TopCommRingCat` on the objects that are complete and Hausdorff for the group uniformity
of their topology. This is the codomain of the adic structure presheaf. -/
noncomputable abbrev CompleteSeparatedTopCommRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun R : TopCommRingCat.{u} ↦ TopCommRingCat.IsCompleteSeparated R)

end TauCeti
