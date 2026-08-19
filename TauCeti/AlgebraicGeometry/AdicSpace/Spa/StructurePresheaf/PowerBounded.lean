/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic
public import TauCeti.RingTheory.Huber.PowerBounded

/-!
# Power-bounded sections of the structure presheaf

Wedhorn §8.1 pairs the structure presheaf with an integral subpresheaf `𝒪_X⁺`. **This file does
not define that object.** It defines the subring of sections all of whose components are
power-bounded, and proves that restriction preserves it — so the assignment is a subpresheaf of
`presentationLimitPresheaf` in the only sense available before sheafification questions arise: a
compatible family of subrings.

## What this is not: the relation to `𝒪_X⁺`

The integral subpresheaf is the *valuation-defined* object

```text
𝒪_X⁺(U) = {f ∈ 𝒪_X(U) : v_x(f_x) ≤ 1 for every x ∈ U}.
```

Power-boundedness of every component is a different predicate, and nothing here relates the two.
Identifying them needs the valuation at a point of `Spa(A,A⁺)` extended to the rational
localizations — an extension this import chain does not have — after which `𝒪_X⁺` should be
*defined* by the displayed condition and its agreement with power-boundedness proved as a
theorem. Until that exists, the declarations below are named for the condition they impose and
claim no `𝒪_X⁺` notation.

## Main definitions

* `TauCeti.ValuationSpectrum.structurePresheafPowerBoundedSubring` : the subring of
  `𝒪_X(V)` of sections with power-bounded components.

## Main results

* `TauCeti.ValuationSpectrum.mem_structurePresheafPowerBoundedSubring_iff` : membership is
  component-wise power-boundedness.
* `TauCeti.ValuationSpectrum.presentationLimitMap_mem_structurePresheafPowerBoundedSubring` :
  restriction preserves the subring, with no continuity input — a restriction's components are a
  subset of the original's (`limit.pre_π`), so the condition is inherited outright.

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
/-- **The power-bounded sections**: the subring of `𝒪_X(V)` of sections all of whose components
are power-bounded — the intersection over the index of the comaps of the power-bounded subrings
of the values. This is not the valuation-defined `𝒪_X⁺`; see the module docstring. -/
noncomputable def structurePresheafPowerBoundedSubring (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) :
    Subring ↥(presentationLimitObj P Aplus V) :=
  ⨅ i : RationalIndex P Aplus V,
    (powerBoundedSubring _).comap
      (show presentationLimitObj P Aplus V ⟶ i.pres.completionLocObj from
        limit.π (rationalIndexDiagram P Aplus V) i).1.1

/-- Membership is power-boundedness of every component. -/
theorem mem_structurePresheafPowerBoundedSubring_iff {f : ↥(presentationLimitObj P Aplus V)} :
    f ∈ structurePresheafPowerBoundedSubring P Aplus V ↔
      ∀ i : RationalIndex P Aplus V, IsPowerBounded
        ((show presentationLimitObj P Aplus V ⟶ i.pres.completionLocObj from
          limit.π (rationalIndexDiagram P Aplus V) i).1.1 f) := by
  simp [structurePresheafPowerBoundedSubring, Subring.mem_iInf]

/-- **Restriction preserves the power-bounded sections**: the components of a restriction are a
subset of the original section's components (`limit.pre_π`), so no continuity or
boundedness of the restriction map enters. -/
theorem presentationLimitMap_mem_structurePresheafPowerBoundedSubring {V W : Opens ↥(spa Aplus)}
    (h : W ≤ V) {f : ↥(presentationLimitObj P Aplus V)}
    (hf : f ∈ structurePresheafPowerBoundedSubring P Aplus V) :
    (presentationLimitMap P h).1.1 f ∈ structurePresheafPowerBoundedSubring P Aplus W := by
  rw [mem_structurePresheafPowerBoundedSubring_iff] at hf ⊢
  intro i
  have hπ := congrArg (fun g ↦ g.1.1 f)
    (limit.pre_π (rationalIndexDiagram P Aplus V) (rationalIndexInclusionOfLE P h) i)
  simpa using hπ ▸ hf ⟨i.pres, i.isOpen_span_num, i.spaRationalOpen_le.trans h⟩

end

end TauCeti.ValuationSpectrum
