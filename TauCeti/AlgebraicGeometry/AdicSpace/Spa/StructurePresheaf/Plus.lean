/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic
public import TauCeti.RingTheory.Huber.PowerBounded

/-!
# The integral structure presheaf `𝒪_X⁺`

Wedhorn §8.1 pairs the structure presheaf with its integral subpresheaf. This file defines the
subring `𝒪_X⁺(V) ⊆ 𝒪_X(V)` of sections all of whose components are power-bounded, and proves
that restriction preserves it — so the assignment is a subpresheaf of `structurePresheaf` in
the only sense available before sheafification questions arise: a compatible family of subrings.

## Main definitions

* `TauCeti.ValuationSpectrum.structurePresheafPlusSubring` : the subring
  `𝒪_X⁺(V) ⊆ 𝒪_X(V)` of sections with power-bounded components.

## Main results

* `TauCeti.ValuationSpectrum.mem_structurePresheafPlusSubring_iff` : membership is
  component-wise power-boundedness.
* `TauCeti.ValuationSpectrum.structurePresheafMap_mem_structurePresheafPlusSubring` :
  restriction preserves `𝒪_X⁺`, with no continuity input — a restriction's components are a
  subset of the original's (`structurePresheafMap_π`), so the condition is inherited outright.

## Why per-component, not power-bounded in the limit ring

`𝒪_X(V)` is itself a topological ring, so "power-bounded in `𝒪_X(V)`" is statable — but a
continuous ring homomorphism need not preserve power-boundedness (`IsPowerBounded.map` needs an
image condition beyond continuity), so restriction-compatibility of that definition is a real
theorem needing real hypotheses. The component-wise definition makes compatibility a reindexing
triviality, and it is the faithful generalisation of the source's per-value definition. The two
agree on components by construction; comparing them on the limit ring is deferred until a
consumer needs it.

## Provenance

Adapted from AINTLIB's `IntegralStructureSheaf.lean` (see References), which defines
`integralPresheafValue D = powerBoundedSubring (presheafValue D)` on each rational value and
stops there — no compatibility with restriction is stated, and the sheaf-cohomology placeholders
in that file are not ported. The generalisation from per-value to a subring of every `𝒪_X(V)`
with restriction-compatibility is new here; the nonarchimedean instance it needs on the values
is `nonarchimedeanRing_locUniformSpace` (`LocalizationTopology/Completion.lean`), added for this
file.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/IntegralStructureSheaf.lean`.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

variable (P) in
/-- **The integral sections** `𝒪_X⁺(V)`: the subring of `𝒪_X(V)` of sections all of whose
components are power-bounded — the intersection over the index of the comaps of the
power-bounded subrings of the values. -/
noncomputable def structurePresheafPlusSubring (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    Subring ↥(structurePresheafObj P Aplus V) :=
  ⨅ i : RationalIndex P Aplus V,
    (powerBoundedSubring _).comap (structurePresheafπ P Aplus V i).1.1

/-- Membership in `𝒪_X⁺(V)` is power-boundedness of every component. -/
theorem mem_structurePresheafPlusSubring_iff {f : ↥(structurePresheafObj P Aplus V)} :
    f ∈ structurePresheafPlusSubring P Aplus V ↔
      ∀ i : RationalIndex P Aplus V, IsPowerBounded ((structurePresheafπ P Aplus V i).1.1 f) := by
  simp [structurePresheafPlusSubring, Subring.mem_iInf]

/-- **Restriction preserves the integral sections**: the components of a restriction are a
subset of the original section's components (`structurePresheafMap_π`), so no continuity or
boundedness of the restriction map enters. -/
theorem structurePresheafMap_mem_structurePresheafPlusSubring {V W : Opens ↥(spa Aplus)}
    (h : W ≤ V) {f : ↥(structurePresheafObj P Aplus V)}
    (hf : f ∈ structurePresheafPlusSubring P Aplus V) :
    (structurePresheafMap P h).1.1 f ∈ structurePresheafPlusSubring P Aplus W := by
  rw [mem_structurePresheafPlusSubring_iff] at hf ⊢
  intro i
  have hπ := congrArg (fun g ↦ g.1.1 f) (structurePresheafMap_π (P := P) h i)
  simpa using hπ ▸ hf ⟨i.pres, i.hopen, i.le_open.trans h⟩

end

end TauCeti.ValuationSpectrum
