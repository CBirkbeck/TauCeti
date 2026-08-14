/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion

/-!
# Restriction between completed rational localisations

A rational subset `U = R(T/s)` of `Spa(A, A⁺)` has many presentations, and the roadmap's Layer 3.1
asks for restriction maps between the coordinate rings of two of them, *satisfying the identity and
composition laws*. This file proves the identity law.

The maps themselves need no new construction: `A⟨T'/s'⟩` supplies the instances that
`existsUnique_continuous_ringHom_completion_locTopology` demands of its target — `CompleteSpace`
and `T0Space` from the completion, `IsUniformAddGroup` from `isUniformAddGroup_locUniformSpace`,
and `NonarchimedeanRing` from `isHuberRing_completion_locTopology`, which must be brought into
scope explicitly or the universal property will not apply. So a restriction map is that universal
property instantiated at another completed localisation, and the laws it satisfies are consequences
of the *uniqueness* half.

The identity law is the first of those: a continuous ring endomorphism of `A⟨T/s⟩` commuting with
the structure map from `A` is the identity, because the identity map commutes too and only one map
can. The composition law follows the same way — a composite of two such maps still commutes with
the structure maps, so it is *the* map — and is left to a follow-up.

The hypotheses are those the universal property needs (`s` a unit, the fractions power-bounded),
not the geometric condition one would prefer. Wedhorn obtains them from an inclusion
`R(T'/s') ⊆ R(T/s)` of rational subsets; that derivation is the substance of the next step and is
not attempted here.

## Main results

* `TauCeti.Huber.PairOfDefinition.eq_id_of_comp_toCompletionLoc`: the identity law.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §8.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **The identity law for restriction maps.** A continuous ring endomorphism of `A⟨T/s⟩`
commuting with the structure map from `A` is the identity: the identity commutes too, and
`existsUnique_continuous_ringHom_completion_locTopology` allows only one such map. -/
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
  -- the target is a completed localisation, so it carries the instances the universal property
  -- demands of its codomain; `NonarchimedeanRing` is the one that needs this line
  have _ := isHuberRing_completion_locTopology P T s S hden
  intro hs hpow g hg hcomp
  obtain ⟨u, -, huniq⟩ := existsUnique_continuous_ringHom_completion_locTopology P T s S hden
    (continuous_toCompletionLoc P T s S hden).continuousAt hs hpow
  rw [huniq g ⟨hg, hcomp⟩, huniq (RingHom.id _) ⟨continuous_id, by ext a; simp⟩]

end PairOfDefinition

end TauCeti.Huber
