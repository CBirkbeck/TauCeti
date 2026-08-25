/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty
public import TauCeti.RingTheory.Huber.LocalizationTopology.Presentation

/-!
# Comparison maps from a containment of rational subsets

`TauCeti.Huber.existsUnique_continuous_ringHom_of_refines` compares two coordinate rings when the
second presentation *refines* the first syntactically — `s'' = s * r` with every `t * r` a
numerator. Wedhorn's Proposition 8.2(1) asks for the comparison under the weaker, geometric
hypothesis that the rational subsets are *contained* in one another, and this file instantiates
Lemma 8.1 at a coordinate ring to get it.

**Neither Proposition 8.2(1) nor presentation independence is proved here.** Lemma 8.1 is
available in this repository only as a reduction to Wedhorn's Proposition 7.52(1), which is
absent, and instantiating it inherits that hypothesis. What is proved below is each of the two
results *given* 7.52(1) for the coordinate rings involved; neither may be cited as the result
Wedhorn states.

> (1) If `U' ⊆ U`, then there exists a unique continuous homomorphism `σ : A⟨T/s⟩ → A⟨T'/s'⟩`
> such that `σ ∘ ρ = ρ'`.

Wedhorn's entire proof is "follows immediately from Lemma 8.1", and so is the one here: the point
of `Spa` is that `Spa ρ'` already factors through `R(T'/s')`
(`spaComapLoc_mem_rationalSubset`), so a containment `R(T'/s') ⊆ R(T/s)` hands the geometric
hypothesis of Lemma 8.1 over directly.

Applying that in both directions to two presentations of the *same* rational subset gives
presentation independence under the same hypothesis: each composite fixes the structure map
from `A`, hence is the identity, so the two coordinate rings are canonically isomorphic. That
is the shape `TauCeti.Huber.presentationRingEquiv` has been waiting for — it produces the
isomorphism *given* comparison maps both ways, and nothing supplies them from an equality of
rational subsets. This file supplies them from 7.52(1) for the two coordinate rings, which is
short of supplying them outright.

## Main results

* `TauCeti.ValuationSpectrum.existsUnique_continuous_ringHom_of_rationalSubset_subset` :
  **Proposition 8.2(1) reduced to Proposition 7.52(1)** — a containment of rational subsets
  induces a unique continuous comparison map of coordinate rings, *given* 7.52(1) for the
  target.
* `TauCeti.ValuationSpectrum.presentationRingEquivOfEq` : **presentation independence reduced
  to the same input** — two presentations of the same rational subset have canonically
  isomorphic coordinate rings, *given* 7.52(1) for both coordinate rings.

## The hypothesis both results carry

Lemma 8.1 needs Wedhorn's Proposition 7.52(1) for its *target*, and 7.52(1) is absent from this
repository — see `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty` for why
it does not follow from a valuative criterion quantifying over all valuations. Instantiating
Lemma 8.1 at a coordinate ring therefore inherits that hypothesis, here `hmem`, together with
openness of the target's maximal ideals, `hmax`.

So these results are *not* unconditional, and the gap is exactly the one
`TauCeti.RingTheory.Huber.LocalizationTopology.Restriction` already names: it records that the
refinement route "removes that dependency" precisely because a refining presentation makes the
fraction distinguished, so that `isPowerBounded_divBy` covers it — which a bare containment does
not. Everything else Lemma 8.1 asks of the target *is* discharged here from what is on main:
power-boundedness of the plus ring by `completedPlusSubring_le_powerBoundedSubring`, the Huber
structure by `isHuberRing_completion_locTopology`, and continuity by
`continuous_toCompletionLoc`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2(1) and
  Lemma 8.1.

## Provenance

Developed here; nothing is ported. AINTLIB reaches presentation independence through a
height-one reduction resting on unproved bodies, which is not followed.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Wedhorn's Proposition 8.2(1) reduced to his Proposition 7.52(1)**, and not 8.2(1) itself:
if the rational subset presented by `T'` over `s'` is contained in the one presented by `T` over
`s`, then exactly one continuous ring homomorphism `A⟨T/s⟩ → A⟨T'/s'⟩` is compatible with the
structure maps from `A` — *provided* the target coordinate ring satisfies 7.52(1).

This is the containment form of `TauCeti.Huber.existsUnique_continuous_ringHom_of_refines`, which
asks instead that the second presentation refine the first syntactically. The proof is Wedhorn's:
`Spa ρ'` factors through `R(T'/s')` by `spaComapLoc_mem_rationalSubset`, so the containment makes
it factor through `R(T/s)`, which is the hypothesis of Lemma 8.1.

The two hypotheses on the target are Lemma 8.1's: `hmax` is openness of the maximal ideals, which
Wedhorn's Proposition 7.52(2) needs, and `hmem` is his Proposition 7.52(1), absent here. -/
theorem existsUnique_continuous_ringHom_of_rationalSubset_subset (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (s' : A) (S' : Type*) [CommRing S']
    [Algebra A S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    (∀ 𝔪 : Ideal (UniformSpace.Completion S'), 𝔪.IsMaximal →
        IsOpen (𝔪 : Set (UniformSpace.Completion S'))) →
    (∀ f : UniformSpace.Completion S',
        (∀ w ∈ spa (completedPlusSubring P Aplus T' s' S' hden'),
          w.toValuativeRel.vle f 1) → f ∈ completedPlusSubring P Aplus T' s' S' hden') →
    ∃! σ : UniformSpace.Completion S →+* UniformSpace.Completion S',
      Continuous σ ∧
        σ.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  let _ := isHuberRing_completion_locTopology P T' s' S' hden'
  intro hmax hmem
  refine existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset P Aplus T s S hden
    (completedPlusSubring P Aplus T' s' S' hden') hmax hmem
    (completedPlusSubring_le_powerBoundedSubring P Aplus hAplus T' s' S' hden')
    (continuous_toCompletionLoc P T' s' S' hden').continuousAt fun w hw ↦ hsub ?_
  -- `Spa ρ'` lands in `R(T'/s')`; the containment carries it into `R(T/s)`
  simpa only [spaComapLoc_val] using
    spaComapLoc_mem_rationalSubset P Aplus T' s' S' hden' ⟨w, hw⟩

/-- **Presentation independence reduced to Wedhorn's Proposition 7.52(1)**, and not presentation
independence itself: two presentations of the *same* rational subset have canonically isomorphic
coordinate rings, *provided* both coordinate rings satisfy 7.52(1).

Wedhorn's Proposition 8.2(1) applies in both directions, and
`TauCeti.Huber.presentationRingEquiv` turns the two comparison maps into an isomorphism — each
composite is compatible with the structure map from `A`, hence is the identity. Supplying those
two maps from an equality of rational subsets is the step that `presentationRingEquiv`'s own
docstring calls "a separate step"; this takes that step as far as 7.52(1) allows.

Each direction carries the target-side hypotheses of Lemma 8.1, so there are two of each: the
primed pair for `A⟨T'/s'⟩` and the unprimed pair for `A⟨T/s⟩`. -/
noncomputable def presentationRingEquivOfEq (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A) (S' : Type*) [CommRing S'] [Algebra A S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    (∀ 𝔪 : Ideal (UniformSpace.Completion S'), 𝔪.IsMaximal →
        IsOpen (𝔪 : Set (UniformSpace.Completion S'))) →
    (∀ f : UniformSpace.Completion S',
        (∀ w ∈ spa (completedPlusSubring P Aplus T' s' S' hden'),
          w.toValuativeRel.vle f 1) → f ∈ completedPlusSubring P Aplus T' s' S' hden') →
    (∀ 𝔪 : Ideal (UniformSpace.Completion S), 𝔪.IsMaximal →
        IsOpen (𝔪 : Set (UniformSpace.Completion S))) →
    (∀ f : UniformSpace.Completion S,
        (∀ w ∈ spa (completedPlusSubring P Aplus T s S hden),
          w.toValuativeRel.vle f 1) → f ∈ completedPlusSubring P Aplus T s S hden) →
    UniformSpace.Completion S ≃+* UniformSpace.Completion S' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro hmax' hmem' hmax hmem
  -- the comparison maps are *data*, so they are extracted with `Exists.choose`; `obtain` would
  -- be eliminating an `ExistsUnique` (a `Prop`) into `Type`
  have hg := existsUnique_continuous_ringHom_of_rationalSubset_subset P Aplus hAplus T s S hden
    T' s' S' hden' heq.ge hmax' hmem'
  have hh := existsUnique_continuous_ringHom_of_rationalSubset_subset P Aplus hAplus T' s' S'
    hden' T s S hden heq.le hmax hmem
  exact presentationRingEquiv P T s S hden T' s' S' hden' hg.choose hh.choose
    hg.choose_spec.1.1 hh.choose_spec.1.1 hg.choose_spec.1.2 hh.choose_spec.1.2

end TauCeti.ValuationSpectrum
