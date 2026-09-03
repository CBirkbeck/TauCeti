/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty

/-!
# The map induced on a quotient of `A⟨X⟩_T`

Wedhorn's Example 6.38(a) presents a rational localisation `A⟨T/s⟩` as a quotient `C ⧸ 𝔞` of a
ring of restricted power series, and one of the two maps that identify them goes *out* of that
quotient. This file supplies it: an evaluation `A⟨X⟩_T →+* B` that kills an ideal `𝔞` factors
through `A⟨X⟩_T ⧸ 𝔞`, and the factorisation is again continuous.

The factorisation itself is `Ideal.Quotient.lift`. What is not already available is its
*continuity*: Mathlib puts the quotient topology on `R ⧸ I`
(`topologicalRingQuotientTopology`) and proves the quotient map open
(`QuotientRing.isOpenMap_coe`), but states nothing about a map lifted out of `R ⧸ I`. The proof
below is the one line that closes that gap — the quotient map is a topological quotient map, so
continuity of the lift is continuity of the evaluation it came from — and it is stated here, at
the point of use, rather than as a general lemma about topological rings.

## What is *not* assumed, and why it is worth saying

`𝔞` is **not** assumed closed. Closedness of `𝔞` is what makes `C ⧸ 𝔞` separated
(`Ideal.Quotient.instT1Space`), and Example 6.38 does need it — but for the *other* direction,
where `C ⧸ 𝔞` is the complete Hausdorff nonarchimedean **target** of the universal property of
`A⟨T/s⟩`, alongside `Ideal.Quotient.instNonarchimedeanRing`. For a map *out* of `C ⧸ 𝔞` none of
that is used: the quotient topology exists for any ideal, and it is all the argument needs. The
hypothesis is therefore omitted rather than carried, and a consumer that also needs `C ⧸ 𝔞` to be
a well-behaved target should assume closedness alongside.

## Main definitions

* `TauCeti.Huber.weightedEvalQuotientHom`: the induced ring homomorphism `A⟨X⟩_T ⧸ 𝔞 →+* B`.

## Main results

* `TauCeti.Huber.weightedEvalQuotientHom_comp_mk`: it is a factorisation of
  `TauCeti.Huber.weightedEvalHom` through the quotient map, which is the property that
  characterises it.
* `TauCeti.Huber.continuous_weightedEvalQuotientHom`: the induced map is continuous.
* `TauCeti.Huber.existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring`: it is the
  *only* continuous homomorphism out of `A⟨X⟩_T ⧸ 𝔞` with the prescribed values on the images of
  the constants and the variables — the universal property of `A⟨X⟩_T` read on the quotient.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Example 6.38(a), and Proposition 5.50 for the
  universal property this factors.
-/

public section

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]
  [T3Space B] {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}

/-- **The map induced on `A⟨X⟩_T ⧸ 𝔞` by an evaluation that kills `𝔞`.** Given the data of the
universal property — `φ` continuous at zero and values `b` making the weighted monomials bounded
— together with an ideal `𝔞` contained in the kernel of the resulting evaluation, this is the
homomorphism `A⟨X⟩_T ⧸ 𝔞 →+* B` through which that evaluation factors.

This is `Ideal.Quotient.lift` at `TauCeti.Huber.weightedEvalHom`; it is named because Example
6.38 uses it twice over, and because its continuity
(`TauCeti.Huber.continuous_weightedEvalQuotientHom`) is the part that is not immediate. -/
noncomputable def weightedEvalQuotientHom (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) {𝔞 : Ideal (weightedRestrictedSubring T hT)}
    (h𝔞 : 𝔞 ≤ RingHom.ker (weightedEvalHom hT hφ hb)) :
    weightedRestrictedSubring T hT ⧸ 𝔞 →+* B :=
  Ideal.Quotient.lift 𝔞 (weightedEvalHom hT hφ hb) fun _ hx ↦ RingHom.mem_ker.mp (h𝔞 hx)

variable {hT : IsWeightFamily T} {hφ : ContinuousAt φ 0} {hb : IsWeightBounded φ T b}
  {𝔞 : Ideal (weightedRestrictedSubring T hT)}
  {h𝔞 : 𝔞 ≤ RingHom.ker (weightedEvalHom hT hφ hb)}

/-- The induced map computes the evaluation on a representative. -/
@[simp]
theorem weightedEvalQuotientHom_mk (f : weightedRestrictedSubring T hT) :
    weightedEvalQuotientHom hT hφ hb h𝔞 (Ideal.Quotient.mk 𝔞 f) = weightedEvalHom hT hφ hb f :=
  (rfl)

/-- **The defining factorisation**: composing the induced map with the quotient map returns the
evaluation. With `Ideal.Quotient.ringHom_ext` this is what pins the induced map down, and it is
the form in which consumers use it. -/
theorem weightedEvalQuotientHom_comp_mk :
    (weightedEvalQuotientHom hT hφ hb h𝔞).comp (Ideal.Quotient.mk 𝔞) =
      weightedEvalHom hT hφ hb :=
  RingHom.ext fun _ ↦ rfl

/-- **The induced map is continuous.** `A⟨X⟩_T ⧸ 𝔞` carries the quotient topology, so the
quotient map is a topological quotient map and continuity of the induced map is exactly
continuity of the evaluation, which is
`TauCeti.Huber.continuous_weightedEvalHom`. -/
theorem continuous_weightedEvalQuotientHom :
    Continuous (weightedEvalQuotientHom hT hφ hb h𝔞) := by
  rw [(QuotientRing.isOpenQuotientMap_mk 𝔞).isQuotientMap.continuous_iff]
  exact continuous_weightedEvalHom hT hφ hb

/-- The induced map sends the class of a constant series to its value under `φ`. -/
@[simp]
theorem weightedEvalQuotientHom_weightedC (a : A) :
    weightedEvalQuotientHom hT hφ hb h𝔞 (Ideal.Quotient.mk 𝔞 (weightedC T hT a)) = φ a := by
  rw [weightedEvalQuotientHom_mk, weightedEvalHom_weightedC]

/-- The induced map sends the class of the `i`-th variable to `bᵢ`. -/
@[simp]
theorem weightedEvalQuotientHom_weightedX (i : Fin k) :
    weightedEvalQuotientHom hT hφ hb h𝔞 (Ideal.Quotient.mk 𝔞 (weightedX T hT i)) = b i := by
  rw [weightedEvalQuotientHom_mk, weightedEvalHom_weightedX]

/-- **The universal property of `A⟨X⟩_T`, read on the quotient.** When `𝔞` lies in the kernel of
the evaluation, there is exactly one continuous ring homomorphism `A⟨X⟩_T ⧸ 𝔞 →+* B` taking the
prescribed values on the images of the constants and of the variables.

Existence is `TauCeti.Huber.weightedEvalQuotientHom`. Uniqueness is the uniqueness clause of
`TauCeti.Huber.existsUnique_continuous_ringHom_weightedRestrictedSubring` transported across the
quotient map: a competitor composed with `Ideal.Quotient.mk` is a continuous homomorphism out of
`A⟨X⟩_T` with the same values on the generators, so it *is* the evaluation, and a homomorphism
out of a quotient is determined by that composite. -/
theorem existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring :
    ∃! ψ : weightedRestrictedSubring T hT ⧸ 𝔞 →+* B, Continuous ψ ∧
      (∀ a, ψ (Ideal.Quotient.mk 𝔞 (weightedC T hT a)) = φ a) ∧
      ∀ i, ψ (Ideal.Quotient.mk 𝔞 (weightedX T hT i)) = b i :=
  ⟨weightedEvalQuotientHom hT hφ hb h𝔞, ⟨continuous_weightedEvalQuotientHom,
      weightedEvalQuotientHom_weightedC, weightedEvalQuotientHom_weightedX⟩,
    fun _ ⟨hψ, hC, hX⟩ ↦ Ideal.Quotient.ringHom_ext <| by
      rw [weightedEvalQuotientHom_comp_mk]
      exact weightedRestrictedSubring_ringHom_ext_of_continuous hT
        (hψ.comp continuous_quot_mk) (continuous_weightedEvalHom hT hφ hb)
        (fun a ↦ (hC a).trans (weightedEvalHom_weightedC hT hφ hb a).symm)
        fun i ↦ (hX i).trans (weightedEvalHom_weightedX hT hφ hb i).symm⟩

end TauCeti.Huber

end
