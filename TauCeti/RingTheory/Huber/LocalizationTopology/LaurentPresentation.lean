/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
public import TauCeti.RingTheory.Huber.WeightedEval.Quotient

/-!
# The Laurent presentation of a one-step refinement

Adjoining one numerator `t` to a rational presentation `(T, s)` gives the refinement
`(T, s) → (insert t T, s)`, and `A⟨(insert t T)/s⟩` is cut out of `A⟨T/s⟩⟨X⟩` by the single
relation `X = t/s`. This file supplies the map that presentation asserts in one direction: a
unique continuous ring homomorphism

```text
A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)  →  A⟨(insert t T)/s⟩
```

sending constants to the restriction map and `X` to `t/s`.

The restriction map itself, and the fact that it carries `t/s` to `t/s`, live one file earlier in
`TauCeti.RingTheory.Huber.LocalizationTopology.Restriction`: they need only the
restriction/localisation theory, not the weighted-evaluation machinery imported here.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.laurentRelationIdeal`: the ideal `(t/s - X)` of `A⟨T/s⟩⟨X⟩`,
  where `t/s` is `TauCeti.Localization.divBy` read in the completion via
  `TauCeti.Huber.PairOfDefinition.toCompletionLoc_mul_unit_inv_eq_divBy`.

## Main results

* `TauCeti.Huber.PairOfDefinition.laurentRelationIdeal_quotientMk_weightedC`: in the quotient,
  the constant `t/s` and the variable `X` agree. This is the relation the ideal imposes.
* `TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_laurentQuotient_restriction`:
  the map above, with its uniqueness.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.55 and
  Proposition 8.30.

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08` analyses this same one-step reduction in
`projects/AdicSpaces/Adic spaces/Wedhorn828.lean`, lines 841-868 and 2774, where it is recorded as
an open step — line 2774 marks it "GENUINE RESIDUAL — the Remark-7.55 relative reduction object for
Prop 8.30". Its construction was therefore not available to port, and no code was taken from it.
Its `divByS` is the localisation-level fraction; the map here is built on the completion-level
bridge this repository already had.
-/

public section

namespace TauCeti.Huber

open TauCeti.Localization

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (T : Finset A) (s t : A)
  (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

/-- **The Laurent relation ideal `(t/s - X)`** of `A⟨T/s⟩⟨X⟩`, the single relation that cuts
`A⟨(insert t T)/s⟩` out of the one-variable restricted series over `A⟨T/s⟩`. -/
noncomputable def laurentRelationIdeal :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    Ideal (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_locUniformSpace P T s S hden
  Ideal.span {weightedC _ isWeightFamily_one_weight ((divBy t s : S) : UniformSpace.Completion S) -
    weightedX _ isWeightFamily_one_weight 0}

/-- Unfolding lemma for `TauCeti.Huber.PairOfDefinition.laurentRelationIdeal`. -/
theorem laurentRelationIdeal_def :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    laurentRelationIdeal P T s t S hden = Ideal.span
      {weightedC _ isWeightFamily_one_weight ((divBy t s : S) : UniformSpace.Completion S) -
        weightedX _ isWeightFamily_one_weight 0} := (rfl)

/-- **The relation the ideal imposes**: in `A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)` the constant `t/s` and the
variable `X` have the same class. This is what a consumer needs, rather than the span. -/
@[simp]
theorem laurentRelationIdeal_quotientMk_weightedC :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
        (weightedC _ isWeightFamily_one_weight ((divBy t s : S) : UniformSpace.Completion S))
      = Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
        (weightedX _ isWeightFamily_one_weight 0) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, laurentRelationIdeal_def]
  exact Ideal.subset_span rfl

section OneStep

variable [DecidableEq A] (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
  (hden' : HasDenominatorPower P (insert t T) s S')

/-- **The Laurent presentation of a one-step refinement, backward half.** There is exactly one
continuous ring homomorphism

```text
A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)  →  A⟨(insert t T)/s⟩
```

restricting to `TauCeti.Huber.PairOfDefinition.restrictionRingHomInsert` on constants, and
sending `X` to `t/s`.

The only fact particular to this situation is
`TauCeti.Huber.PairOfDefinition.restrictionRingHomInsert_coe_divBy`; everything else is the
universal property
`TauCeti.Huber.existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring` of the
quotient. Wedhorn's Remark 7.55 chains such one-step refinements, and Proposition 8.30 reduces
flatness of a general restriction map along that chain to this elementary case. -/
theorem existsUnique_continuous_ringHom_laurentQuotient_restriction :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P (insert t T) s S' hden'
    letI := isUniformAddGroup_locUniformSpace P (insert t T) s S' hden'
    letI := isTopologicalRing_locUniformSpace P (insert t T) s S' hden'
    letI := isHuberRing_locUniformSpace P (insert t T) s S' hden'
    ∃! ψ : (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight) ⧸
          laurentRelationIdeal P T s t S hden →+* UniformSpace.Completion S',
      Continuous ψ ∧
      (∀ a, ψ (Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a)) =
        restrictionRingHomInsert P T s S hden t S' hden' a) ∧
      ∀ i, ψ (Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i)) =
        ((divBy t s : S') : UniformSpace.Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P (insert t T) s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P (insert t T) s S' hden'
  have _ := isTopologicalRing_locUniformSpace P (insert t T) s S' hden'
  have _ := isHuberRing_locUniformSpace P (insert t T) s S' hden'
  have hu' : IsUnit (toCompletionLoc P (insert t T) s S' hden' s) :=
    isUnit_toCompletionLoc_of_dvd P (insert t T) s S' hden' dvd_rfl
  set φ := restrictionRingHomInsert P T s S hden t S' hden' with hφdef
  have hφ : ContinuousAt φ 0 :=
    (continuous_restrictionRingHomInsert P T s S hden t S' hden').continuousAt
  set b : Fin 1 → UniformSpace.Completion S' :=
    fun _ ↦ ((divBy t s : S') : UniformSpace.Completion S') with hbdef
  have hb : IsWeightBounded φ (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) b :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).2 fun _ ↦ by
      rw [hbdef, ← toCompletionLoc_mul_unit_inv_eq_divBy P (insert t T) s S' hden' t hu']
      exact isPowerBounded_toCompletionLoc_mul_unit_inv P (insert t T) s S' hden'
        (mul_one s).symm hu' (by simp)
  -- the evaluation kills `t/s - X`, so the relation ideal lands in its kernel
  have h𝔞 : laurentRelationIdeal P T s t S hden ≤
      RingHom.ker (weightedEvalHom isWeightFamily_one_weight hφ hb) := by
    rw [laurentRelationIdeal_def, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      RingHom.mem_ker, map_sub, weightedEvalHom_weightedC, weightedEvalHom_weightedX,
      sub_eq_zero]
    exact restrictionRingHomInsert_coe_divBy P T s S hden t S' hden'
  exact existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring
    isWeightFamily_one_weight hφ hb h𝔞

end OneStep

end PairOfDefinition

end TauCeti.Huber

end
