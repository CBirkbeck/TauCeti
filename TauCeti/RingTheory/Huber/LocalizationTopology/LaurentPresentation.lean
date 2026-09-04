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

## Main definitions

* `TauCeti.Huber.PairOfDefinition.laurentRelationIdeal`: the ideal `(t/s - X)` of `A⟨T/s⟩⟨X⟩`,
  where `t/s` is `TauCeti.Localization.divBy` read in the completion via
  `TauCeti.Huber.PairOfDefinition.toCompletionLoc_mul_unit_inv_eq_divBy`.

## Main results

* `TauCeti.Huber.PairOfDefinition.restrictionRingHomInsert_coe_divBy`: the restriction map
  carries `t/s` to `t/s`. This is the only fact particular to the refinement.
* `TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_laurentQuotient_restriction`:
  the map above, with its uniqueness.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.55 and
  Proposition 8.30.
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

section OneStep

variable [DecidableEq A] (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
  (hden' : HasDenominatorPower P (insert t T) s S')

/-- **The restriction map of a one-step numerator adjunction.** Adjoining `t` to the numerators
refines `(T, s)` to `(insert t T, s)` with cofactor `1`, so `TauCeti.Huber.restrictionRingHom`
applies; this names the resulting map. -/
noncomputable def restrictionRingHomInsert :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P (insert t T) s S' hden'
    letI := isUniformAddGroup_locUniformSpace P (insert t T) s S' hden'
    letI := isTopologicalRing_locUniformSpace P (insert t T) s S' hden'
    UniformSpace.Completion S →+* UniformSpace.Completion S' :=
  restrictionRingHom P T s S hden (insert t T) s S' hden' 1 (mul_one s).symm
    fun u hu ↦ by simpa using Finset.mem_insert_of_mem hu

/-- The one-step restriction map is continuous. -/
theorem continuous_restrictionRingHomInsert :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P (insert t T) s S' hden'
    letI := isUniformAddGroup_locUniformSpace P (insert t T) s S' hden'
    letI := isTopologicalRing_locUniformSpace P (insert t T) s S' hden'
    Continuous (restrictionRingHomInsert P T s t S hden S' hden') :=
  continuous_restrictionRingHom P T s S hden (insert t T) s S' hden' 1 (mul_one s).symm
    fun u hu ↦ by simpa using Finset.mem_insert_of_mem hu

/-- **The one-step restriction map carries `t/s` to `t/s`.** This is the only fact particular to
the refinement `(T, s) → (insert t T, s)`; everything else in the presentation below is the
universal property of the quotient.

Both structure maps from `A` commute with restriction, so `t` goes to `t` and `s` goes to `s`.
The image of `s⁻¹` is then forced: it and the inverse downstairs are both inverses of the image
of `s`, and inverses in a monoid are unique. -/
theorem restrictionRingHomInsert_coe_divBy :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P (insert t T) s S' hden'
    letI := isUniformAddGroup_locUniformSpace P (insert t T) s S' hden'
    letI := isTopologicalRing_locUniformSpace P (insert t T) s S' hden'
    restrictionRingHomInsert P T s t S hden S' hden' ((divBy t s : S) : UniformSpace.Completion S)
      = ((divBy t s : S') : UniformSpace.Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P (insert t T) s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P (insert t T) s S' hden'
  have _ := isTopologicalRing_locUniformSpace P (insert t T) s S' hden'
  have hs : s = s * 1 := (mul_one s).symm
  have hTsub : ∀ u ∈ T, u * 1 ∈ insert t T := fun u hu ↦ by
    simpa using Finset.mem_insert_of_mem hu
  have hu : IsUnit (toCompletionLoc P T s S hden s) :=
    isUnit_toCompletionLoc_of_dvd P T s S hden dvd_rfl
  have hu' : IsUnit (toCompletionLoc P (insert t T) s S' hden' s) :=
    isUnit_toCompletionLoc_of_dvd P (insert t T) s S' hden' dvd_rfl
  set φ := restrictionRingHomInsert P T s t S hden S' hden' with hφdef
  have hcomp : ∀ a, φ (toCompletionLoc P T s S hden a)
      = toCompletionLoc P (insert t T) s S' hden' a := fun a ↦ by
    rw [hφdef, restrictionRingHomInsert, ← RingHom.comp_apply,
      restrictionRingHom_comp_toCompletionLoc P T s S hden (insert t T) s S' hden' 1 hs hTsub]
  have hinv : φ (↑hu.unit⁻¹) = ↑hu'.unit⁻¹ := by
    have h : (↑hu.unit⁻¹ : UniformSpace.Completion S) * ↑hu.unit = 1 := hu.unit.inv_mul
    rw [hu.unit_spec] at h
    have hmul : φ (↑hu.unit⁻¹) * ↑hu'.unit = 1 := by
      rw [hu'.unit_spec, ← hcomp s, ← map_mul, h, map_one]
    exact (Units.inv_eq_of_mul_eq_one_left hmul).symm
  rw [← toCompletionLoc_mul_unit_inv_eq_divBy P T s S hden t hu,
    ← toCompletionLoc_mul_unit_inv_eq_divBy P (insert t T) s S' hden' t hu',
    map_mul, hcomp t, hinv]

/-- **The Laurent presentation of a one-step refinement, backward half.** There is exactly one
continuous ring homomorphism

```text
A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)  →  A⟨(insert t T)/s⟩
```

restricting to `TauCeti.Huber.PairOfDefinition.restrictionRingHomInsert` on constants, and
sending `X` to `t/s`.

The only fact particular to this situation is
`TauCeti.Huber.restrictionRingHomInsert_toCompletionLocDiv`; everything else is the universal
property `TauCeti.Huber.existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring` of the
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
        restrictionRingHomInsert P T s t S hden S' hden' a) ∧
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
  set φ := restrictionRingHomInsert P T s t S hden S' hden' with hφdef
  have hφ : ContinuousAt φ 0 :=
    (continuous_restrictionRingHomInsert P T s t S hden S' hden').continuousAt
  have hu' : IsUnit (toCompletionLoc P (insert t T) s S' hden' s) :=
    isUnit_toCompletionLoc_of_dvd P (insert t T) s S' hden' dvd_rfl
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
    rw [laurentRelationIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      RingHom.mem_ker, map_sub, weightedEvalHom_weightedC, weightedEvalHom_weightedX,
      sub_eq_zero]
    exact restrictionRingHomInsert_coe_divBy P T s t S hden S' hden'
  exact existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring
    isWeightFamily_one_weight hφ hb h𝔞

end OneStep

end PairOfDefinition

end TauCeti.Huber

end
