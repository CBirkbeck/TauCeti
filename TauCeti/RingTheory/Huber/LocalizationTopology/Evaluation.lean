/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion

/-!
# Evaluating `A⟨X₁, …, Xₖ⟩` at the fractions of a rational localisation

This file constructs the map that presents a rational localisation over its base:

```text
A⟨X₁, …, Xₖ⟩ → A⟨T/s⟩,      Xᵢ ↦ tᵢ/s
```

for numerators `t₁, …, tₖ` drawn from `T`. It is the map Wedhorn's Examples 6.38 and 6.39 use to
exhibit `A⟨T/s⟩` as topologically of finite type over `A`.

## Main results

* `TauCeti.Huber.PairOfDefinition.isPowerBounded_divBy_completion`: a distinguished fraction
  `t/s` with `t ∈ T` is power-bounded in `A⟨T/s⟩`. This is the hypothesis the universal property
  needs, and it is where membership in `T` is used.
* `TauCeti.Huber.PairOfDefinition.rationalEvalHom`: the evaluation map itself, with
  `TauCeti.Huber.PairOfDefinition.continuous_rationalEvalHom`,
  `TauCeti.Huber.PairOfDefinition.rationalEvalHom_coe_weightedC` and
  `TauCeti.Huber.PairOfDefinition.rationalEvalHom_coe_weightedX` as its interface. Uniqueness is
  `TauCeti.Huber.existsUnique_continuous_ringHom_completion_weightedRestrictedSubring`, which
  already characterises any continuous homomorphism by these two evaluations.

## What this is not

**Nothing here says the map is surjective**, and surjectivity is what Wedhorn's Examples 6.38 and
6.39 are actually about. What is constructed is the map; whether it is onto — equivalently, by
`TauCeti.Huber.isStrictlyTopologicallyFiniteType_of_surjective`, whether `A⟨T/s⟩` is strictly
topologically of finite type over `A` — is left open here.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50 for the
  universal property, and Examples 6.38 and 6.39 for the presentation.
-/

public section

namespace TauCeti.Huber

open UniformSpace TauCeti.Localization

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

namespace PairOfDefinition

variable (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*)
  [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)

/-- **A distinguished fraction is power-bounded in `A⟨T/s⟩`.** The completion companion of
`TauCeti.Huber.isPowerBounded_divBy_locUniformSpace`: the fraction is power-bounded already in
`Aₛ`, because it lies in the bounded ring of definition `A₀[T/s]`, and
`TauCeti.Huber.isPowerBounded_completion_coe_of_isPowerBounded` carries that to the completion.

Named because this is the shape `TauCeti.Huber.weightedEvalHomCompletion` consumes, and it is the
one place membership in `T` is used: for an arbitrary `t : A` the fraction `t/s` need not be
power-bounded, which is why a rational localisation is indexed by a *set* of numerators. -/
theorem isPowerBounded_divBy_completion {t : A} (ht : t ∈ T) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsPowerBounded (((divBy t s : S) : Completion S)) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_locUniformSpace P T s S hden
  isPowerBounded_completion_coe_of_isPowerBounded
    (isPowerBounded_divBy_locUniformSpace P T s S hden ht)

/-- **The evaluation map `A⟨X₁, …, Xₖ⟩ → A⟨T/s⟩`**, sending each variable `Xᵢ` to the fraction
`tᵢ/s` and each constant to its image under the structure map.

It is `TauCeti.Huber.weightedEvalHomCompletion` — Wedhorn's Proposition 5.50 carried to the
completion — at the trivial weight family, where the domain is `A⟨X₁, …, Xₖ⟩` itself. The
numerators are given as a family `t : Fin k → A` landing in `T` rather than as `T` itself, so
that a caller may repeat or omit numerators; what their membership buys is
`isPowerBounded_divBy_completion`, the hypothesis the universal property needs. -/
noncomputable def rationalEvalHom {k : ℕ} (t : Fin k → A) (ht : ∀ i, t i ∈ T) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    restrictedMvPowerSeriesCompletion k A →+* Completion S :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_locUniformSpace P T s S hden
  weightedEvalHomCompletion (φ := toCompletionLoc P T s S hden)
    (b := fun i ↦ ((divBy (t i) s : S) : Completion S)) isWeightFamily_one_weight
    (continuous_toCompletionLoc P T s S hden).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).2
      fun i ↦ isPowerBounded_divBy_completion P T s S hden (ht i))

variable {k : ℕ} (t : Fin k → A) (ht : ∀ i, t i ∈ T)

/-- The evaluation map is continuous. -/
theorem continuous_rationalEvalHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Continuous (rationalEvalHom P T s S hden t ht) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_locUniformSpace P T s S hden
  continuous_weightedEvalHomCompletion _ _ _

/-- The evaluation map sends a constant to its image under the structure map `A → A⟨T/s⟩`. -/
@[simp]
theorem rationalEvalHom_coe_weightedC (a : A) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    rationalEvalHom P T s S hden t ht
        ((weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight a :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion k A)
      = toCompletionLoc P T s S hden a := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  rw [rationalEvalHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

/-- **The evaluation map sends `Xᵢ` to `tᵢ/s`** — the defining property. -/
@[simp]
theorem rationalEvalHom_coe_weightedX (i : Fin k) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    rationalEvalHom P T s S hden t ht
        ((weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion k A)
      = ((divBy (t i) s : S) : Completion S) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  rw [rationalEvalHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

end PairOfDefinition

end TauCeti.Huber

end
