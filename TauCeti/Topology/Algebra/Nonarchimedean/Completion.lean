/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Completion
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Completions of nonarchimedean groups and rings

Three facts about the Hausdorff completion that need only the additive, resp. ring, structure:
the closure of the image of an open additive subgroup is open, the closure of the image of a
*closed* additive subgroup pulls back along the completion map to the subgroup itself, and the
kernel of the completion map is the closure of the zero ideal.

They are stated here rather than alongside the Huber-ring theory that uses them, since none of
them mentions a pair of definition or an adic topology, and they live in the
`UniformSpace.Completion` namespace of the construction they describe rather than in a `TauCeti`
one.

## Main results

* `UniformSpace.Completion.isOpen_closure_image_coe`: the closure in `Â` of the image of an open
  additive subgroup of `A` is open.
* `UniformSpace.Completion.preimage_closure_image_coe`: the preimage in `A` of the closure of the
  image of a closed additive subgroup is the subgroup itself.
* `UniformSpace.Completion.ker_coeRingHom`: the kernel of `A → Â` is the closure of `⊥`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.32 and Example 5.33, for
  the completion of a topological group and ring; `ker_coeRingHom` is the statement there that
  the completion map has kernel `closure {0}`.
* Mathlib's `Mathlib/Topology/Algebra/Nonarchimedean/Completion.lean`, whose
  `Completion.isDenseInducing_coe` all three proofs go through.
-/

public section

open UniformSpace

namespace UniformSpace.Completion

section AddGroup

variable {A : Type*} [AddCommGroup A] [UniformSpace A] [IsUniformAddGroup A]

/-- The closure in the completion of the image of an open additive subgroup is open. Only the
additive structure is involved. -/
theorem isOpen_closure_image_coe {G : AddSubgroup A} (hG : IsOpen (G : Set A)) :
    IsOpen (closure (((↑) : A → Completion A) '' (G : Set A))) := by
  have hmem := Completion.isDenseInducing_coe.closure_image_mem_nhds (hG.mem_nhds G.zero_mem)
  rw [Completion.coe_zero] at hmem
  exact AddSubgroup.isOpen_of_mem_nhds ((G.map Completion.toCompl).topologicalClosure) hmem

omit [IsUniformAddGroup A] in
/-- The preimage under `A → Â` of the closure of the image of a closed additive subgroup `G` is
`G` itself, so a closed subgroup is recovered from its image in the completion.

Companion to `isOpen_closure_image_coe`, which says that for an *open* `G` that same closure is
open in `Â`; this one says what it pulls back to, and asks only that `G` be closed. Closedness is
the real content: `A` need not be Hausdorff, so `A → Â` need not be injective, and it is `G` being
closed that collapses the preimage to `G` rather than to `G + closure {0}`. An open subgroup is
closed (`AddSubgroup.isClosed_of_isOpen`), which is how the open case is obtained. -/
@[simp]
theorem preimage_closure_image_coe {G : AddSubgroup A} (hG : IsClosed (G : Set A)) :
    ((↑) : A → Completion A) ⁻¹' closure (((↑) : A → Completion A) '' (G : Set A)) =
      (G : Set A) := by
  -- The completion map is inducing, so the left-hand side is the closure of `G` in `A`.
  rw [← Completion.isDenseInducing_coe.isInducing.closure_eq_preimage_closure_image, hG.closure_eq]

end AddGroup

section Ker

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-- The kernel of the completion map `A → Â` is the closure of the zero ideal. -/
theorem ker_coeRingHom :
    RingHom.ker (Completion.coeRingHom : A →+* Completion A) = (⊥ : Ideal A).closure := by
  ext x
  rw [RingHom.mem_ker, ← SetLike.mem_coe, Ideal.coe_closure]
  calc (Completion.coeRingHom x = 0)
      ↔ ((x : Completion A) = ((0 : A) : Completion A)) := by rw [Completion.coe_zero]; rfl
    _ ↔ Inseparable ((x : Completion A)) (((0 : A) : Completion A)) := inseparable_iff_eq.symm
    _ ↔ Inseparable x (0 : A) := Completion.isDenseInducing_coe.isInducing.inseparable_iff
    _ ↔ x - 0 ∈ closure ({0} : Set A) := addGroup_inseparable_iff
    _ ↔ x ∈ closure ((⊥ : Ideal A) : Set A) := by rw [sub_zero]; simp

end Ker

end UniformSpace.Completion
