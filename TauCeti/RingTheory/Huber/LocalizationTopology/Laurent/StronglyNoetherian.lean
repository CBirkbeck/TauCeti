/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Identification
public import TauCeti.RingTheory.Huber.StronglyNoetherian

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable
import TauCeti.Topology.Algebra.GroupCompletion

/-!
# Strong noetherianness of a completed rational localisation

**Preservation of strong noetherianness by a numerator enlargement.** This is not Wedhorn's
Proposition 8.30, whose stated conclusion is flatness; it is the auxiliary result that
proposition is proved from. The flatness statement itself lives in
`TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Flat`, which consumes what is proved here.

The argument is the chain of Wedhorn's Remark 7.55. Adjoining a single numerator `t` presents the
enlarged localisation as a quotient of a one-variable restricted power-series algebra over the
smaller one, by `TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv`. For a **topologically
nilpotent** denominator the presenting ideal is then closed as soon as that smaller ring is
strongly noetherian, by
`TauCeti.Huber.PairOfDefinition.isClosed_laurentRelationIdeal_of_isStronglyNoetherian`. Given the
nilpotence, one hypothesis therefore carries the whole induction: strong noetherianness of the
base both closes the ideal and, through `IsOpenQuotientMap.isStronglyNoetherian`, passes to the
quotient. Nilpotence is asked only of a genuine enlargement — for `T' = T` there is nothing to
prove.

Only the *topology* varies along the chain. The localisation `S` itself is fixed, because
`IsLocalization.Away s S` does not mention the numerators, so each step is a `hden.mono` away and
the base case of the induction is the hypothesis itself.

## Main results

* `TauCeti.Huber.PairOfDefinition.isStronglyNoetherian_completion_of_isClosed` : one enlargement
  step, with the presenting ideal assumed closed.
* `TauCeti.Huber.PairOfDefinition`
  `.isStronglyNoetherian_completion_of_isTopologicallyNilpotent` : the same step with closedness
  discharged, which is the form the induction consumes.
* `TauCeti.Huber.PairOfDefinition.isStronglyNoetherian_completion_of_subset` : the chain form.
  Strong noetherianness propagates from `T` to every `T' ⊇ T`, which is what
  `TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset_union` assumes at every proper
  intermediate presentation.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.30 and
  Remark 7.55.
-/

public section

namespace TauCeti.Huber

open TauCeti.Localization

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (T : Finset A) (s t : A)
  (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)
  (T' : Finset A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
  (hden' : HasDenominatorPower P T' s S') (hTT' : ∀ u ∈ T, u ∈ T')

include hTT' in
/-- Adjoining one numerator preserves strong noetherianness of the completed localisation. -/
theorem isStronglyNoetherian_completion_of_isClosed (ht : t ∈ T')
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl :
      letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight)))
    (hSN :
      letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    IsStronglyNoetherian (UniformSpace.Completion S') := by
  let := locUniformSpace P T s S hden
  let := isUniformAddGroup_locUniformSpace P T s S hden
  let := isTopologicalRing_locUniformSpace P T s S hden
  let := isHuberRing_locUniformSpace P T s S hden
  let := locUniformSpace P T' s S' hden'
  let := isUniformAddGroup_locUniformSpace P T' s S' hden'
  let := isTopologicalRing_locUniformSpace P T' s S' hden'
  let := isHuberRing_locUniformSpace P T' s S' hden'
  have : IsStronglyNoetherian (UniformSpace.Completion S) := hSN
  have h₁ : IsOpenQuotientMap
      ⇑(restrictedMvPowerSeriesCompletionEquiv 1 (UniformSpace.Completion S)) :=
    (Homeomorph.mk (restrictedMvPowerSeriesCompletionEquiv 1 (UniformSpace.Completion S)).toEquiv
      (uniformContinuous_restrictedMvPowerSeriesCompletionEquiv
        (k := 1) (A := UniformSpace.Completion S)).continuous
      (uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm
        (k := 1) (A := UniformSpace.Completion S)).continuous).isOpenQuotientMap
  have h₂ : IsOpenQuotientMap
      ⇑(laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl) :=
    (Homeomorph.mk (laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl).toEquiv
      (continuous_laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl)
      (continuous_laurentQuotientRingEquiv_symm P T s t S hden T' S' hden' hTT' ht hsplit
        hcl)).isOpenQuotientMap
  exact IsOpenQuotientMap.isStronglyNoetherian
    (π := (laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl).toRingHom.comp
      ((Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)).comp
        (restrictedMvPowerSeriesCompletionEquiv 1 (UniformSpace.Completion S)).toRingHom))
    (h₂.comp ((QuotientRing.isOpenQuotientMap_mk _).comp h₁))

-- Two presentations with the same numerator set, carried by different localisations, have
-- isomorphic completions: the restriction maps in both directions compose to the identity. Strong
-- noetherianness therefore transfers with nothing assumed -- no nilpotence, no noetherianity.
private theorem isStronglyNoetherian_completion_self (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
    (hden' : HasDenominatorPower P T s S')
    (hSN :
      letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI := locUniformSpace P T s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T s S' hden'
    letI := isTopologicalRing_locUniformSpace P T s S' hden'
    letI := isHuberRing_locUniformSpace P T s S' hden'
    IsStronglyNoetherian (UniformSpace.Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T s S' hden'
  have _ := isHuberRing_locUniformSpace P T s S' hden'
  have h : (restrictionRingHomOfSubset P T s S' hden' T S hden fun _ hu ↦ hu).comp
      (restrictionRingHomOfSubset P T s S hden T S' hden' fun _ hu ↦ hu) = RingHom.id _ := by
    simp
  have h' : (restrictionRingHomOfSubset P T s S hden T S' hden' fun _ hu ↦ hu).comp
      (restrictionRingHomOfSubset P T s S' hden' T S hden fun _ hu ↦ hu) = RingHom.id _ := by
    simp
  exact (isStronglyNoetherian_congr
    (RingEquiv.ofRingHom (restrictionRingHomOfSubset P T s S hden T S' hden' fun _ hu ↦ hu)
      (restrictionRingHomOfSubset P T s S' hden' T S hden fun _ hu ↦ hu) h' h)
    (continuous_restrictionRingHomOfSubset P T s S hden T S' hden' fun _ hu ↦ hu)
    (continuous_restrictionRingHomOfSubset P T s S' hden' T S hden fun _ hu ↦ hu)).mp hSN

include hTT' in
/-- **The Laurent step preserves strong noetherianness, for a topologically nilpotent
denominator.** The closedness hypothesis of
`TauCeti.Huber.PairOfDefinition.isStronglyNoetherian_completion_of_isClosed` is then discharged
by the base's own strong noetherianness, so the two uses of `hSN` are the whole content: it
closes the relation ideal, and it feeds the open quotient. This is the form the induction over
the numerators consumes. -/
theorem isStronglyNoetherian_completion_of_isTopologicallyNilpotent
    (hnil : t ∉ T → IsTopologicallyNilpotent s) (ht : t ∈ T')
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hSN :
      letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    IsStronglyNoetherian (UniformSpace.Completion S') := by
  by_cases htT : t ∈ T
  · -- `t` was already a numerator, so `T' = T` and this is the identity enlargement
    have hT'T : T' = T :=
      Finset.Subset.antisymm (fun u hu ↦ (hsplit u hu).elim id fun h ↦ h ▸ htT) hTT'
    subst hT'T
    exact isStronglyNoetherian_completion_self P T' s S hden S' hden' hSN
  · exact isStronglyNoetherian_completion_of_isClosed P T s t S hden T' S' hden' hTT' ht hsplit
      (isClosed_laurentRelationIdeal_of_isStronglyNoetherian P T s t S hden (hnil htT) hSN) hSN


-- The induction behind Proposition 8.30: strong noetherianness propagates from `T` to `T ∪ W`
-- one numerator at a time. Only the topology on `S` varies; the localisation itself is fixed.
-- Nilpotence is asked only of a genuine enlargement, so the empty case assumes nothing.
private theorem isStronglyNoetherian_completion_union [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (hTT' : T ⊆ T') (hnil : T ⊂ T' → IsTopologicallyNilpotent s)
    (hSN :
      letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    ∀ (W V : Finset A), V = T ∪ W → W ⊆ T' \ T → ∀ hV : T ⊆ V,
    letI := locUniformSpace P V s S (hden.mono hV)
    letI := isUniformAddGroup_locUniformSpace P V s S (hden.mono hV)
    letI := isTopologicalRing_locUniformSpace P V s S (hden.mono hV)
    letI := isHuberRing_locUniformSpace P V s S (hden.mono hV)
    IsStronglyNoetherian (UniformSpace.Completion S) := by
  classical
  intro W
  induction W using Finset.induction_on with
  | empty =>
    intro V hVdef _ hV
    rw [Finset.union_empty] at hVdef
    subst hVdef
    exact hSN
  | @insert a W haW ih =>
    intro V hVdef hW hV
    rw [Finset.union_insert] at hVdef
    subst hVdef
    have hTU : T ⊆ T ∪ W := Finset.subset_union_left
    have hUV : T ∪ W ⊆ insert a (T ∪ W) := Finset.subset_insert _ _
    have hWsub : W ⊆ T' \ T := fun x hx ↦ hW (Finset.mem_insert_of_mem hx)
    -- `a` lies in `T'` and outside `T`, so the enlargement `T ⊆ T'` is proper and `hnil` applies
    have ha := Finset.mem_sdiff.mp (hW (Finset.mem_insert_self a W))
    exact isStronglyNoetherian_completion_of_isTopologicallyNilpotent P (T ∪ W) s a S
      (hden.mono hTU) (insert a (T ∪ W)) S (hden.mono hV) hUV
      (fun _ ↦ hnil ⟨hTT', fun h ↦ ha.2 (h ha.1)⟩)
      (Finset.mem_insert_self _ _)
      (fun u hu ↦ (Finset.mem_insert.mp hu).symm.imp id id)
      (ih (T ∪ W) rfl hWsub hTU)

/-- **Strong noetherianness is preserved by a numerator enlargement.** If the completed
localisation carrying the `T`-topology is strongly noetherian, then it is strongly noetherian for
the `T'`-topology of any `T' ⊇ T`. Topological nilpotence of the denominator is asked only of a
*proper* enlargement: for `T' = T` the conclusion is the hypothesis.

This is the auxiliary preservation result that Wedhorn's Proposition 8.30 is proved from, not the
proposition itself, whose conclusion is flatness. It is what
`TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset_union` assumes: that lemma asks
for strong noetherianness at every proper intermediate presentation, and this supplies it from
strong noetherianness at `T` alone. -/
theorem isStronglyNoetherian_completion_of_subset (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (hTT' : T ⊆ T')
    (hnil : T ⊂ T' → IsTopologicallyNilpotent s)
    (hSN :
      letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI := locUniformSpace P T' s S (hden.mono hTT')
    letI := isUniformAddGroup_locUniformSpace P T' s S (hden.mono hTT')
    letI := isTopologicalRing_locUniformSpace P T' s S (hden.mono hTT')
    letI := isHuberRing_locUniformSpace P T' s S (hden.mono hTT')
    IsStronglyNoetherian (UniformSpace.Completion S) := by
  classical
  exact isStronglyNoetherian_completion_union P T s S hden T' hTT' hnil hSN (T' \ T) T'
    (by rw [Finset.union_sdiff_self_eq_union]; exact (Finset.union_eq_right.mpr hTT').symm)
    Finset.Subset.rfl hTT'


end PairOfDefinition

end TauCeti.Huber

end
