/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion

/-!
# Restriction between completed rational localisations

A rational subset `U = R(T/s)` of `Spa(A, A⁺)` has many presentations, and the roadmap's Layer 3.1
asks for the maps relating the coordinate rings of two of them. This file supplies the underlying
existence-and-uniqueness statement: given presentations `(T, s)` and `(T', s')`, if `s` becomes a
unit in `A⟨T'/s'⟩` and each fraction `t/s` becomes power-bounded there, then there is exactly one
continuous ring homomorphism

```text
A⟨T/s⟩ → A⟨T'/s'⟩
```

commuting with the two structure maps from `A`.

This is `existsUnique_continuous_ringHom_completion_locTopology` applied with the target being the
*other* completed localisation rather than an arbitrary complete Huber ring. What makes that
legitimate is that `A⟨T'/s'⟩` supplies the instances the universal property demands of its target:
`CompleteSpace` and `T0Space` come from the completion, `IsUniformAddGroup` from
`isUniformAddGroup_locUniformSpace`, and `NonarchimedeanRing` from
`isHuberRing_completion_locTopology` — that last one has to be in scope before the universal
property will apply.

The hypotheses are the ones the universal property needs, not the geometric condition one would
prefer. Wedhorn obtains them from an inclusion `R(T'/s') ⊆ R(T/s)` of rational subsets; deriving
them from such an inclusion is the next step and is not attempted here.

## Main results

* `TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_restrict`: the restriction map
  between two completed rational localisations exists and is unique.
* `TauCeti.Huber.PairOfDefinition.eq_id_of_comp_toCompletionLoc`: the identity law — a continuous
  endomorphism of `A⟨T/s⟩` fixing the structure map is the identity.

## Implementation notes

The results are stated as an `∃!` rather than as a named map with a separate continuity lemma.
Naming the map via `Exists.choose` typechecks, but the accompanying
`Continuous (locRestrict …)` statement then has to re-elaborate a type carrying six `letI`-bound
instances, and that exceeds the elaboration budget. Since the repository forbids `maxHeartbeats`
overrides, the named map is deferred rather than forced; the uniqueness half is what downstream
laws actually use, and `eq_id_of_comp_toCompletionLoc` shows the pattern — the composition law
follows the same way, by checking that a composite satisfies the defining clause.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §8.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **The restriction map between two completed rational localisations exists and is unique.**

If `s` is a unit in `A⟨T'/s'⟩` and every fraction `t/s` is power-bounded there, then exactly one
continuous ring homomorphism `A⟨T/s⟩ → A⟨T'/s'⟩` commutes with the structure maps from `A`. -/
theorem existsUnique_continuous_ringHom_restrict (P : PairOfDefinition A) (T T' : Finset A)
    (s s' : A) (S S' : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden : HasDenominatorPower P T s S) (hden' : HasDenominatorPower P T' s' S') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (hs : IsUnit (toCompletionLoc P T' s' S' hden' s)),
      (∀ t ∈ T, IsPowerBounded (toCompletionLoc P T' s' S' hden' t * ↑hs.unit⁻¹)) →
      ∃! g : UniformSpace.Completion S →+* UniformSpace.Completion S',
        Continuous g ∧
          g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  -- without this the target is not known to be nonarchimedean and the universal property
  -- will not apply
  have _ := isHuberRing_completion_locTopology P T' s' S' hden'
  exact fun hs hpow ↦ existsUnique_continuous_ringHom_completion_locTopology P T s S hden
    (continuous_toCompletionLoc P T' s' S' hden').continuousAt hs hpow

/-- **The identity law for restriction.** A continuous endomorphism of `A⟨T/s⟩` commuting with the
structure map from `A` is the identity, because the identity does so too and such a map is
unique. -/
theorem eq_id_of_comp_toCompletionLoc (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (hs : IsUnit (toCompletionLoc P T s S hden s))
      (_ : ∀ t ∈ T, IsPowerBounded (toCompletionLoc P T s S hden t * ↑hs.unit⁻¹))
      (g : UniformSpace.Completion S →+* UniformSpace.Completion S), Continuous g →
      g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T s S hden →
      g = RingHom.id (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  intro hs hpow g hg hcomp
  obtain ⟨u, -, huniq⟩ := existsUnique_continuous_ringHom_restrict P T T s s S S hden hden hs hpow
  rw [huniq g ⟨hg, hcomp⟩, huniq (RingHom.id _) ⟨continuous_id, by ext a; simp⟩]

end PairOfDefinition

end TauCeti.Huber
