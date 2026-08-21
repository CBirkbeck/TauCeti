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

Three facts about the Hausdorff completion: the closure of the image of an open additive
subgroup is open, a closed set is the preimage of the closure of its image, and the kernel of the
completion map is the closure of the zero ideal. The first needs only the additive structure and
the last the ring structure; the middle one needs neither, being about the inducing map alone.

They are stated here rather than alongside the Huber-ring theory that uses them, since none of
them mentions a pair of definition or an adic topology, and they live in the
`UniformSpace.Completion` namespace of the construction they describe rather than in a `TauCeti`
one.

## Main results

* `UniformSpace.Completion.isOpen_closure_image_coe`: the closure in `Â` of the image of an open
  additive subgroup of `A` is open.
* `UniformSpace.Completion.preimage_closure_image_coe`: a *closed set* is the preimage of the
  closure of its image, so membership downstairs can be tested upstairs.
* `UniformSpace.Completion.ker_coeRingHom`: the kernel of `A → Â` is the closure of `⊥`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.32 and Example 5.33, for
  the completion of a topological group and ring; `ker_coeRingHom` is the statement there that
  the completion map has kernel `closure {0}`.
* `Completion.isDenseInducing_coe`, which all three proofs go through, is declared in Mathlib's
  `Mathlib/Topology/UniformSpace/Completion.lean`; the nonarchimedean file of the same name
  supplies the openness machinery `isOpen_closure_image_coe` uses, not that lemma.
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

end AddGroup

section ClosedSet

variable {A : Type*} [UniformSpace A]

/-- **A closed set is the preimage of the closure of its image in the completion.** `A → Â` is an
inducing map, so the closure of any set is the preimage of the closure of its image; for a closed
set the left-hand side is the set itself.

This is the form a consumer meets: it decides membership in `s` by a closure computation
upstairs in `Â`, without unfolding the generic inducing-map argument each time. There is no
closure on the `A` side — closedness of `s` is exactly what removes it.

Closedness is not decoration. `A` need not be Hausdorff, so `A → Â` need not be injective: in
general the preimage of the closure of the image of a subgroup `G` is `G + closure {0}` rather
than `G`, and it is `IsClosed s` that collapses the difference. No algebraic structure enters —
for a closed additive subgroup `G`, apply this to `(G : Set A)`. -/
@[simp]
theorem preimage_closure_image_coe {s : Set A} (hs : IsClosed s) :
    ((↑) : A → Completion A) ⁻¹' closure (((↑) : A → Completion A) '' s) = s := by
  rw [← Completion.isDenseInducing_coe.isInducing.closure_eq_preimage_closure_image, hs.closure_eq]

end ClosedSet

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
