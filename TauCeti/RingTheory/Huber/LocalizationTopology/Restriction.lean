/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion

/-!
# Maps out of `A⟨T/s⟩` are determined on `A`

A continuous ring homomorphism out of the completed rational localisation `A⟨T/s⟩` is determined
by its restriction to `A`. That is the extensionality principle behind the maps relating the
coordinate rings of two presentations of a rational subset, which roadmap Layer 3.1 asks for
*satisfying the identity and composition laws*: both laws are corollaries, because each says that
two maps agreeing on `A` coincide.



Both laws are corollaries of one extensionality principle, `hom_ext_toCompletionLoc`, which lives
with the completion itself in `TauCeti.RingTheory.Huber.LocalizationTopology.Completion` because it
is about maps out of `A⟨T/s⟩` and mentions no second presentation. In particular neither law needs
the *existence* hypotheses — `s` a unit, the fractions power-bounded — since those are what make a
map exist, not what makes two of them equal.

## Main results

* `TauCeti.Huber.PairOfDefinition.eq_id_of_comp_toCompletionLoc`: the identity law.
* `TauCeti.Huber.PairOfDefinition.eq_comp_of_comp_toCompletionLoc`: the composition law.

## Provenance

Original. The extensionality argument is the standard "localise, then complete" one; the two
inputs are Mathlib's `IsLocalization.ringHom_ext`
(`Mathlib/RingTheory/Localization/Defs.lean`) and `UniformSpace.Completion.ext`
(`Mathlib/Topology/UniformSpace/Completion.lean`). AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, branch `dev/adic-spaces` at `37bbdaeb9`) was
swept: it models rational presentations in `RationalSubsets.lean` but carries no corresponding
extensionality lemma for the completed localisation. Nothing was copied.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §8.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **The identity law.** A continuous ring endomorphism of `A⟨T/s⟩` fixing the structure map from
`A` is the identity, since the identity fixes it too. -/
theorem eq_id_of_comp_toCompletionLoc (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S), Continuous g →
      g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T s S hden →
      g = RingHom.id (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro g hg hcomp
  refine hom_ext_toCompletionLoc P T s S hden g (RingHom.id _) hg continuous_id ?_
  rw [RingHom.id_comp]
  exact hcomp

/-- **The composition law.** For three presentations, a continuous ring homomorphism
`A⟨T/s⟩ → A⟨T''/s''⟩` compatible with the structure maps is the composite of the maps through
`A⟨T'/s'⟩`, since the composite is compatible too. -/
theorem eq_comp_of_comp_toCompletionLoc (P : PairOfDefinition A) (T T' T'' : Finset A)
    (s s' s'' : A) (S S' S'' : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    [CommRing S''] [Algebra A S''] [IsLocalization.Away s'' S'']
    (hden : HasDenominatorPower P T s S) (hden' : HasDenominatorPower P T' s' S')
    (hden'' : HasDenominatorPower P T'' s'' S'') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    letI := locUniformSpace P T'' s'' S'' hden''
    letI := isUniformAddGroup_locUniformSpace P T'' s'' S'' hden''
    letI := isTopologicalRing_locUniformSpace P T'' s'' S'' hden''
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S'), Continuous g →
      g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' →
      ∀ (h : UniformSpace.Completion S' →+* UniformSpace.Completion S''), Continuous h →
      h.comp (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T'' s'' S'' hden'' →
      ∀ (k : UniformSpace.Completion S →+* UniformSpace.Completion S''), Continuous k →
      k.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T'' s'' S'' hden'' →
      k = h.comp g := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  let _ := locUniformSpace P T'' s'' S'' hden''
  have _ := isUniformAddGroup_locUniformSpace P T'' s'' S'' hden''
  have _ := isTopologicalRing_locUniformSpace P T'' s'' S'' hden''
  intro g hg hgc h hh hhc k hk hkc
  refine hom_ext_toCompletionLoc P T s S hden k (h.comp g) hk (hh.comp hg) ?_
  rw [RingHom.comp_assoc, hgc, hhc]
  exact hkc

end PairOfDefinition

end TauCeti.Huber
