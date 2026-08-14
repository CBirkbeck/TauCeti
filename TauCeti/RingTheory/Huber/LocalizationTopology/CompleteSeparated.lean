/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated

/-!
# `A⟨T/s⟩` is a complete separated topological ring

The adic structure presheaf (roadmap Layer 3.3) assigns `A⟨T/s⟩` to the rational subset `R(T/s)`,
and its values are required to be *complete separated* topological rings (*Adic Spaces*,
arXiv:1910.05934v1, §8.1–§8.2). This module is that bridge: it exhibits `A⟨T/s⟩` as an object of
`CompleteSeparatedTopCommRingCat`, so that the presheaf can be written down with that category as
its codomain.

Nothing here is deep — `A⟨T/s⟩` is a separated completion, so it is complete and Hausdorff for its
own uniformity, and `isCompleteSeparated_of_completeSpace_of_t0Space` transfers that to the
predicate on the associated object. What the module supplies is the *bookkeeping*: `locTopology` is
not an instance, so the uniform structures on `Aₛ` are not in scope by inference, and a consumer
would otherwise repeat the three-declaration preamble `locUniformSpace`,
`isUniformAddGroup_locUniformSpace`, `isTopologicalRing_locUniformSpace` at every use. The
declarations below carry it once.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.completionLocObj` : `A⟨T/s⟩` as an object of
  `CompleteSeparatedTopCommRingCat` — the value the structure presheaf takes on `R(T/s)`.

## Main results

* `TauCeti.Huber.PairOfDefinition.isCompleteSeparated_completion_locTopology` : `A⟨T/s⟩` is
  complete separated.
* `TauCeti.Huber.PairOfDefinition.completionLocObj_obj` : the underlying `TopCommRingCat` of that
  object is `UniformSpace.Completion S` with the topology `locUniformSpace` induces.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1–§8.2, where the structure
  presheaf of an adic space is built with complete separated topological rings as its codomain.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.51, §5.6, for `A⟨T/s⟩`
  itself, which `LocalizationTopology.Completion` constructs.
-/

namespace TauCeti.Huber

open TauCeti.TopCommRingCat

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-! ### `A⟨T/s⟩` as an object of `CompleteSeparatedTopCommRingCat` -/

/-- **`A⟨T/s⟩` is complete separated**: the separated completion of `Aₛ` under `locTopology` is
complete and Hausdorff, hence complete separated as a topological ring.

This is `isCompleteSeparated_of_completeSpace_of_t0Space` at the completion's own instances. It is
named here, rather than left to the caller as the general statement for a completion is, because
`locTopology` is not an instance: applying the general form takes the three-declaration preamble
`locUniformSpace`, `isUniformAddGroup_locUniformSpace`, `isTopologicalRing_locUniformSpace`, which
the statement below carries. -/
theorem isCompleteSeparated_completion_locTopology [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsCompleteSeparated (TopCommRingCat.of (UniformSpace.Completion S)) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  isCompleteSeparated_of_completeSpace_of_t0Space _

/-- **`A⟨T/s⟩` as an object of `CompleteSeparatedTopCommRingCat`**: the value the adic structure
presheaf takes on the rational subset `R(T/s)`.

`completionLocObj_obj` identifies the underlying object; the body is not exported, so that is how
a consumer computes with it. -/
noncomputable def completionLocObj [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) : CompleteSeparatedTopCommRingCat :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  CompleteSeparatedTopCommRingCat.of (UniformSpace.Completion S)

/-- The underlying topological ring of `completionLocObj` is `A⟨T/s⟩` itself: the completion of
`Aₛ` for the uniformity `locUniformSpace`. -/
@[simp]
theorem completionLocObj_obj [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (completionLocObj P T s S hden).obj = TopCommRingCat.of (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  exact CompleteSeparatedTopCommRingCat.of_obj _

end PairOfDefinition

end

end TauCeti.Huber
