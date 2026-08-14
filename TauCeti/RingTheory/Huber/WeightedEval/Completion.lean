/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty
public import Mathlib.Topology.Algebra.UniformRing

/-!
# The universal property of the completed algebra of `A⟨X⟩_T`

Wedhorn's Proposition 5.50 (`existsUnique_continuous_ringHom_weightedRestrictedSubring`) is the
universal property of the restricted-series ring `A⟨X⟩_T` itself. This file carries it across the
separated completion: a ring homomorphism `φ : A →+* B` into a complete Hausdorff nonarchimedean
ring, continuous at zero, together with weight-bounded values `bᵢ`, extends to the completion of
`A⟨X⟩_T` in exactly one continuous way.

Neither half is new mathematics; both compose 5.50 with a standard property of the completion.
Existence is `UniformSpace.Completion.extensionHom` applied to the evaluation homomorphism, which
is available exactly because the target is already assumed complete and Hausdorff — the same
hypotheses 5.50 carries, so the completed statement asks for nothing extra. Uniqueness is
`UniformSpace.Completion.ext`: two continuous maps out of a completion that agree on the image of
the coercion are equal, and agreement there is 5.50's own uniqueness clause applied to the
restrictions along `UniformSpace.Completion.coeRingHom`.

At the trivial weight family `Tᵢ = {1}` the completion is the algebra the roadmap writes
`A⟨X₁,…,Xₖ⟩` for an arbitrary Tate ring, so this is that algebra's universal property. It is
stated for a general weight family because nothing in the argument uses triviality.

## Main definitions

* `TauCeti.Huber.completionEvalHom` : the evaluation homomorphism of 5.50, extended to the
  completion.

## Main results

* `TauCeti.Huber.existsUnique_continuous_ringHom_completion` :
  Proposition 5.50 for the completion of `A⟨X⟩_T`.
* `TauCeti.Huber.completionEvalHom_weightedC` and
  `TauCeti.Huber.completionEvalHom_weightedX` : its values on the constants and the variables.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 5.50.
-/

public section

namespace TauCeti.Huber

open UniformSpace

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]
  [T3Space B] {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}

/-- The evaluation homomorphism of Proposition 5.50, extended to the completion of `A⟨X⟩_T`.
The extension exists because the target is complete and Hausdorff. -/
@[expose] noncomputable def completionEvalHom (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) :
    Completion (weightedRestrictedSubring T hT) →+* B :=
  Completion.extensionHom (weightedEvalHom hT hφ hb) (continuous_weightedEvalHom hT hφ hb)

@[simp]
theorem completionEvalHom_coe (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (f : weightedRestrictedSubring T hT) :
    completionEvalHom hT hφ hb (f : Completion (weightedRestrictedSubring T hT))
      = weightedEvalHom hT hφ hb f :=
  Completion.extensionHom_coe (weightedEvalHom hT hφ hb) (continuous_weightedEvalHom hT hφ hb) f

theorem continuous_completionEvalHom (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) : Continuous (completionEvalHom hT hφ hb) :=
  Completion.continuous_extension

/-- The value on a constant. Not a `simp` lemma: `simp` reaches it through
`completionEvalHom_coe` and `weightedEvalHom_weightedC` already. -/
theorem completionEvalHom_weightedC (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (a : A) :
    completionEvalHom hT hφ hb
      ((weightedC T hT a : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = φ a := by
  rw [completionEvalHom_coe, weightedEvalHom_weightedC]

/-- The value on a variable. Not a `simp` lemma, for the same reason as
`completionEvalHom_weightedC`. -/
theorem completionEvalHom_weightedX (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (i : Fin k) :
    completionEvalHom hT hφ hb
      ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i := by
  rw [completionEvalHom_coe, weightedEvalHom_weightedX]

/-- **The universal property of the completion of `A⟨X⟩_T`, under `IsWeightBounded`.** Given
`φ : A →+* B` continuous at zero and weight-bounded values `b`, there is exactly one continuous
ring homomorphism from the completion of `A⟨X⟩_T` to `B` restricting to `φ` on the constants and
sending each `Xᵢ` to `bᵢ`.

This mirrors `existsUnique_continuous_ringHom_weightedRestrictedSubring`, the uncompleted
statement under the same uniform hypothesis. Proposition 5.50's own hypothesis is the
coordinatewise one, so the theorem to cite as 5.50 is
`existsUnique_continuous_ringHom_completion_of_isWeightedVarPowerBounded` below.

As in the uncompleted statement, uniqueness is among *continuous* homomorphisms. Here that is not
a convenience: the completion is a closure of the image of `A⟨X⟩_T`, so the values on that image
determine a continuous map and nothing else. -/
theorem existsUnique_continuous_ringHom_completion (hT : IsWeightFamily T)
    (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ T b) :
    ∃! ψ : Completion (weightedRestrictedSubring T hT) →+* B, Continuous ψ ∧
      (∀ a, ψ ((weightedC T hT a : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) = φ a) ∧
      ∀ i, ψ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i := by
  refine ⟨completionEvalHom hT hφ hb, ⟨continuous_completionEvalHom hT hφ hb,
    completionEvalHom_weightedC hT hφ hb, completionEvalHom_weightedX hT hφ hb⟩, ?_⟩
  rintro ψ ⟨hψc, hψC, hψX⟩
  -- Restricted along the coercion, `ψ` is a continuous ring map out of `A⟨X⟩_T` taking the values
  -- Proposition 5.50 pins down, so it is the evaluation homomorphism there.
  have key : ψ.comp Completion.coeRingHom = weightedEvalHom hT hφ hb :=
    (existsUnique_continuous_ringHom_weightedRestrictedSubring hT hφ hb).unique
      ⟨hψc.comp (Completion.continuous_coe _), hψC, hψX⟩
      ⟨continuous_weightedEvalHom hT hφ hb, weightedEvalHom_weightedC hT hφ hb,
        weightedEvalHom_weightedX hT hφ hb⟩
  -- Two continuous maps out of a completion agreeing on that image are equal.
  refine DFunLike.coe_injective
    (Completion.ext hψc (continuous_completionEvalHom hT hφ hb) fun f ↦ ?_)
  rw [completionEvalHom_coe]
  exact congrArg (fun g : weightedRestrictedSubring T hT →+* B ↦ g f) key

/-- **Wedhorn 5.50 for the completed algebra**, under the hypothesis Proposition 5.50 itself
carries: each weighted variable `φ(Tᵢ) · bᵢ` power-bounded as a set, one index at a time.

This is the theorem to cite as 5.50 for the completion. It is the statement above composed with
`isWeightBounded_of_isWeightedVarPowerBounded`, exactly as
`existsUnique_continuous_ringHom_weightedRestrictedSubring_of_isWeightedVarPowerBounded` relates
to its own uniform form. -/
theorem existsUnique_continuous_ringHom_completion_of_isWeightedVarPowerBounded
    (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0) (hb : IsWeightedVarPowerBounded φ T b) :
    ∃! ψ : Completion (weightedRestrictedSubring T hT) →+* B, Continuous ψ ∧
      (∀ a, ψ ((weightedC T hT a : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) = φ a) ∧
      ∀ i, ψ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i :=
  existsUnique_continuous_ringHom_completion hT hφ (isWeightBounded_of_isWeightedVarPowerBounded hb)

end TauCeti.Huber
