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

**Neither result is yet Wedhorn's in the generality he states it.** Instantiating Lemma 8.1 at a
coordinate ring inherits what Lemma 8.1 asks of a target pair, and below that is two hypotheses
carried rather than derived: openness of the target's maximal ideals, and openness of the plus
subring `A_U⁺`. Until both are discharged neither result may be cited as the statement Wedhorn
gives. See *The hypotheses both results carry* for why each is still there.

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
rational subsets. This file supplies them, assuming only that the coordinate rings' plus subrings
are open.

## Main results

* `TauCeti.ValuationSpectrum.existsUnique_continuous_ringHom_of_rationalSubset_subset` :
  **Wedhorn's Proposition 8.2(1)** — a containment of rational subsets induces a unique
  continuous comparison map of coordinate rings.
* `TauCeti.ValuationSpectrum.presentationRingEquivOfEq` : **presentation independence** — two
  presentations of the same rational subset have canonically isomorphic coordinate rings.

## The hypotheses both results carry

Wedhorn's Proposition 7.52(1) is no longer among them. It landed in #4552 as
`TauCeti.ValuationSpectrum.mem_of_forall_vle_one` and is consumed inside Lemma 8.1, so
instantiating Lemma 8.1 at a coordinate ring no longer inherits it. What each instantiation does
inherit is what 7.52(1) asks of that coordinate ring as a *pair*:

* `hmax`, openness of the target's maximal ideals — carried rather than derived, because the
  route through `Ideal.isOpen_of_isMaximal_of_isOpen_isTopologicallyNilpotent` wants
  `IsLinearTopology`, which by `IsTateRing.isOpen_iff_eq_top` no nonzero Tate ring has;
* openness of the plus subring `A_U⁺`, which is **not** proved anywhere on main and is the one
  remaining obligation of this file. It is a strictly smaller one than the `hmem` it replaces:
  `hmem` was "prove Wedhorn 7.52(1) at this coordinate ring", whereas this is a single concrete
  topological fact about a subring the repository already constructs. Integral closedness needs
  no hypothesis at all — `isIntegrallyClosedIn_completedPlusSubring` is an instance, because
  `completedPlusSubring` is *defined* as an integral closure.

The gap that remains is exactly the one
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

/-- **Wedhorn's Proposition 8.2(1)**: if the rational subset presented by `T'` over `s'` is
contained in the one presented by `T` over `s`, then exactly one continuous ring homomorphism
`A⟨T/s⟩ → A⟨T'/s'⟩` is compatible with the structure maps from `A`.

This is the containment form of `TauCeti.Huber.existsUnique_continuous_ringHom_of_refines`, which
asks instead that the second presentation refine the first syntactically. The proof is Wedhorn's:
`Spa ρ'` factors through `R(T'/s')` by `spaComapLoc_mem_rationalSubset`, so the containment makes
it factor through `R(T/s)`, which is the hypothesis of Lemma 8.1.

The two hypotheses on the target are Lemma 8.1's, and neither is Proposition 7.52(1) — that is
now consumed inside Lemma 8.1 itself. `hmax` is openness of the maximal ideals, which Wedhorn's
Proposition 7.52(2) needs; the second is openness of the target's plus subring `A_U⁺`, which
7.52(1) asks of the pair and which is not proved anywhere on main. Integral closedness of `A_U⁺`
needs no hypothesis: `isIntegrallyClosedIn_completedPlusSubring` is an instance. -/
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
    IsOpen ((completedPlusSubring P Aplus T' s' S' hden' :
      Subring (UniformSpace.Completion S')) : Set (UniformSpace.Completion S')) →
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
  intro hmax hopen'
  refine existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset P Aplus T s S hden
    (completedPlusSubring P Aplus T' s' S' hden') hmax hopen'
    (completedPlusSubring_le_powerBoundedSubring P Aplus hAplus T' s' S' hden')
    (continuous_toCompletionLoc P T' s' S' hden').continuousAt fun w hw ↦ hsub ?_
  -- `Spa ρ'` lands in `R(T'/s')`; the containment carries it into `R(T/s)`
  simpa only [spaComapLoc_val] using
    spaComapLoc_mem_rationalSubset P Aplus T' s' S' hden' ⟨w, hw⟩

/-- **Presentation independence**: two presentations of the *same* rational subset have
canonically isomorphic coordinate rings.

Wedhorn's Proposition 8.2(1) applies in both directions, and
`TauCeti.Huber.presentationRingEquiv` turns the two comparison maps into an isomorphism — each
composite is compatible with the structure map from `A`, hence is the identity. Supplying those
two maps from an equality of rational subsets is the step that `presentationRingEquiv`'s own
docstring calls "a separate step"; this takes that step.

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
    IsOpen ((completedPlusSubring P Aplus T' s' S' hden' :
      Subring (UniformSpace.Completion S')) : Set (UniformSpace.Completion S')) →
    (∀ 𝔪 : Ideal (UniformSpace.Completion S), 𝔪.IsMaximal →
        IsOpen (𝔪 : Set (UniformSpace.Completion S))) →
    IsOpen ((completedPlusSubring P Aplus T s S hden :
      Subring (UniformSpace.Completion S)) : Set (UniformSpace.Completion S)) →
    UniformSpace.Completion S ≃+* UniformSpace.Completion S' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  let _ := isHuberRing_completion_locTopology P T s S hden
  let _ := isHuberRing_completion_locTopology P T' s' S' hden'
  intro hmax' hopen' hmax hopen
  -- the comparison maps are *data*, so they are extracted with `Exists.choose`; `obtain` would
  -- be eliminating an `ExistsUnique` (a `Prop`) into `Type`
  have hg := existsUnique_continuous_ringHom_of_rationalSubset_subset P Aplus hAplus T s S hden
    T' s' S' hden' heq.ge hmax' hopen'
  have hh := existsUnique_continuous_ringHom_of_rationalSubset_subset P Aplus hAplus T' s' S'
    hden' T s S hden heq.le hmax hopen
  exact presentationRingEquiv P T s S hden T' s' S' hden' hg.choose hh.choose
    hg.choose_spec.1.1 hh.choose_spec.1.1 hg.choose_spec.1.2 hh.choose_spec.1.2

end TauCeti.ValuationSpectrum
