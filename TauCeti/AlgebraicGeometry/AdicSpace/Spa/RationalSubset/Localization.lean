/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Basic

/-!
# A containment of rational subsets presents the smaller one over the larger

`TauCeti.Huber.PairOfDefinition.restrictionRingHom` builds the map `A⟨T/s⟩ → A⟨T''/s''⟩` from a
*refinement* of presentations: a factorisation `s'' = s * r` together with `t * r ∈ T''` for every
`t ∈ T`, and a `HasDenominatorPower` for the target. A containment of rational subsets supplies
none of that on its face.

This file closes the gap, and it is the first place where the `Spa` side and the localisation
topology meet. Given the containment `R(T'/s') ⊆ R(T/s)` **together with a `HasDenominatorPower`
for each of the two presentations it compares**, it produces a presentation `(T'', s * s')` of the
smaller subset which *is* a refinement of `(T, s)` — exactly the three inputs `restrictionRingHom`
asks for, with `r = s'`.

What the containment buys is the *third* hypothesis: only the denominator condition for the
product presentation is derived here. The two input ones are assumed, as they must be — a
containment of subsets says nothing about how either localisation is topologised.

Both halves are already on `main` and are composed here rather than reproved: the refined
numerator set is `TauCeti.ValuationSpectrum.exists_refinement_of_subset`, and the denominator
hypothesis for the product denominator is
`TauCeti.Huber.PairOfDefinition.hasDenominatorPower_mul`.

## Main results

* `TauCeti.ValuationSpectrum.exists_refinement_hasDenominatorPower_of_subset`: a containment of
  rational subsets yields a refining presentation of the smaller one whose `HasDenominatorPower`
  holds, so the restriction map onto it is defined.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.2.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **A containment of rational subsets refines the presentation.** If `R(T'/s') ⊆ R(T/s)`, and
each of the two presentations carries a `HasDenominatorPower`, then the smaller subset has a
presentation `(T'', s * s')` which refines `(T, s)` along `r = s'` and whose own denominator
hypothesis holds in any localisation away from `s * s'`.

Only that last condition is derived; `hden` and `hden'` are hypotheses, since a containment of
subsets carries no information about the topologies on `S` and `S'`.

These are precisely the inputs of
`TauCeti.Huber.PairOfDefinition.restrictionRingHom … s' rfl hT`, so a consumer obtains the
restriction map `A⟨T/s⟩ → A⟨T''/(s * s')⟩` with no further obligation. -/
theorem exists_refinement_hasDenominatorPower_of_subset (P : PairOfDefinition A)
    (Aplus : Subring A) (T T' : Finset A) (s s' : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (S'' : Type*) [CommRing S''] [Algebra A S''] [IsLocalization.Away (s * s') S'']
    (hden : HasDenominatorPower P T s S) (hden' : HasDenominatorPower P T' s' S')
    (h : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    ∃ T'' : Finset A, rationalSubset Aplus T' s' = rationalSubset Aplus T'' (s * s')
      ∧ (∀ t ∈ T, t * s' ∈ T'') ∧ HasDenominatorPower P T'' (s * s') S'' := by
  obtain ⟨T'', hset, hT, hT'⟩ := exists_refinement_of_subset Aplus T T' s s' h
  exact ⟨T'', hset, hT, hasDenominatorPower_mul P T T' T'' s s' S S' S'' hT hT' hden hden'⟩

end TauCeti.ValuationSpectrum

end
