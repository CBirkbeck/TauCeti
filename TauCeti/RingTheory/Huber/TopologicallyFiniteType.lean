/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Completion

/-!
# Homomorphisms topologically of finite type

Wedhorn's §6.6. A ring homomorphism `φ : A → B` into a complete `f`-adic ring is *topologically of
finite type* when `B` is presented as a quotient of a weighted restricted power-series algebra
`A⟨X₁, …, Xₖ⟩_T` over `A` — by a map that is surjective, continuous and open, and is a map of
`A`-algebras. It is *strictly* topologically of finite type when the trivial weight family
`Tᵢ = {1}` suffices, so that the presenting algebra is the ordinary `A⟨X₁, …, Xₖ⟩`.

The notion is what three results the adic-spaces roadmap needs are stated in terms of: the second
half of Proposition and Definition 6.36 (a Tate ring is strongly noetherian exactly when every
Tate ring topologically of finite type over it is noetherian), Remark 6.37(1), and Example 6.38,
which Proposition 8.30 cites by name.

## The weighted algebra, and why not the Tate-only one

The presenting algebra is the **weighted** `A⟨X⟩_T`, not `A⟨X⟩`. That is Wedhorn's own Proposition
and Definition 6.29(i), and it is what the roadmap asks for (`AdicSpaces/README.md`, §5.2): the
Tate-only algebra is too narrow downstream, since `A_inf` is Huber and not Tate. Definition 6.28,
the strict variant, is the Tate-only case; the implication between them is
`IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType`.

Two conditions on the weight family are in play and they are not the same. Wedhorn's standing
hypothesis on `T` — needed even to *form* `A⟨X⟩_T` — is `TauCeti.Huber.IsWeightFamily`, that
`Tᵢ^m · U` is a neighbourhood of zero for every `m` and every neighbourhood `U` of zero. The
phrasing in 6.29(i), that each `Tᵢ · A` is open, is the `U = ⊤` case, and is recovered from it by
`TauCeti.Huber.IsWeightFamily.isOpen_weightMul_top`; the converse is not available here (see that
lemma's docstring). Finiteness of each `Tᵢ` is a separate requirement of 6.29(i) — it is what makes
the notion one of *finite* type — and is carried explicitly, since `IsWeightFamily` does not imply
it.

Wedhorn writes the presenting algebra `Â⟨X₁, …, Xₖ⟩_T`, with the completion taken after forming the
restricted series; `UniformSpace.Completion (weightedRestrictedSubring T hT)` is that algebra, and
is what the roadmap writes `A⟨X₁, …, Xₖ⟩_T`.

## Main definitions

* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType`: Wedhorn Definition 6.28.
* `TauCeti.Huber.IsTopologicallyFiniteType`: Wedhorn Proposition and Definition 6.29(i).

## Main results

* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType`: strictly
  topologically of finite type implies topologically of finite type, by the trivial weight family.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §6.6, Definition 6.28 and
  Proposition and Definition 6.29.
-/

public section

namespace TauCeti.Huber

open UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {B : Type*} [CommRing B] [TopologicalSpace B]

/-- **Wedhorn Proposition and Definition 6.29(i)**: `φ : A → B` is *topologically of finite type*
when `B` is presented, as an `A`-algebra, by a surjective continuous open homomorphism out of a
weighted restricted power-series algebra `A⟨X₁, …, Xₖ⟩_T` on finitely many variables with each
weight `Tᵢ` finite. -/
def IsTopologicallyFiniteType (φ : A →+* B) : Prop :=
  ∃ (k : ℕ) (T : Fin k → Set A) (_ : ∀ i, (T i).Finite) (hT : IsWeightFamily T)
    (π : Completion (weightedRestrictedSubring T hT) →+* B),
    Function.Surjective π ∧ Continuous π ∧ IsOpenMap π ∧
      π.comp (Completion.coeRingHom.comp (weightedC T hT)) = φ

/-- Unfolding lemma for the sealed definition `TauCeti.Huber.IsTopologicallyFiniteType`. -/
theorem isTopologicallyFiniteType_iff {φ : A →+* B} :
    IsTopologicallyFiniteType φ ↔
      ∃ (k : ℕ) (T : Fin k → Set A) (_ : ∀ i, (T i).Finite) (hT : IsWeightFamily T)
        (π : Completion (weightedRestrictedSubring T hT) →+* B),
        Function.Surjective π ∧ Continuous π ∧ IsOpenMap π ∧
          π.comp (Completion.coeRingHom.comp (weightedC T hT)) = φ :=
  (Iff.rfl)

/-- **Wedhorn Definition 6.28**: `φ : A → B` is *strictly* topologically of finite type when the
presenting algebra can be taken to be the ordinary `A⟨X₁, …, Xₖ⟩`, the trivial weight family. -/
def IsStrictlyTopologicallyFiniteType (φ : A →+* B) : Prop :=
  ∃ (k : ℕ) (π : Completion (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) →+* B),
    Function.Surjective π ∧ Continuous π ∧ IsOpenMap π ∧
      π.comp (Completion.coeRingHom.comp (weightedC _ isWeightFamily_one_weight)) = φ

/-- Unfolding lemma for the sealed definition
`TauCeti.Huber.IsStrictlyTopologicallyFiniteType`. -/
theorem isStrictlyTopologicallyFiniteType_iff {φ : A →+* B} :
    IsStrictlyTopologicallyFiniteType φ ↔
      ∃ (k : ℕ) (π : Completion (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
          isWeightFamily_one_weight) →+* B),
        Function.Surjective π ∧ Continuous π ∧ IsOpenMap π ∧
          π.comp (Completion.coeRingHom.comp (weightedC _ isWeightFamily_one_weight)) = φ :=
  (Iff.rfl)

/-- The trivial weight family is finite and satisfies the standing hypothesis, so a strict
presentation is a presentation. -/
theorem IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType {φ : A →+* B}
    (h : IsStrictlyTopologicallyFiniteType φ) : IsTopologicallyFiniteType φ := by
  obtain ⟨k, π, hsurj, hcont, hopen, hcomm⟩ := h
  exact ⟨k, _, fun _ ↦ Set.finite_singleton 1, isWeightFamily_one_weight, π, hsurj, hcont, hopen,
    hcomm⟩

end TauCeti.Huber
