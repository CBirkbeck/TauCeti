/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty
public import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# The map induced on a quotient of `A⟨X⟩_T`

Wedhorn's Example 6.38(a) presents a rational localisation `A⟨T/s⟩` as a quotient `C ⧸ 𝔞` of a
ring of restricted power series, and one of the two maps that identify them goes *out* of that
quotient. This file supplies it: an evaluation `A⟨X⟩_T →+* B` that kills an ideal `𝔞` factors
through `A⟨X⟩_T ⧸ 𝔞`, and the factorisation is again continuous.

The factorisation itself is `Ideal.Quotient.lift`, and its continuity is
`continuous_coinduced_dom`: Mathlib gives `R ⧸ I` the coinduced (quotient) topology, so a map out
of it is continuous exactly when its composite with the quotient map is — which is
`TauCeti.Huber.continuous_weightedEvalHom`.

## Relation to `TauCeti.Huber.Pair.Hom.quotientLift`

This repository already carries the same move one level up, for **morphisms of Huber pairs**:
`Pair.Hom.quotientLift` factors a `Hom S T` killing `J` through `S.quotient J`, by the same
`Ideal.Quotient.lift` and the same `continuous_coinduced_dom` step. This file is *not* an instance
of it and cannot be phrased as one: `A⟨X⟩_T` and `B` enter Wedhorn 5.50 as plain topological rings,
with no ring of integral elements and so no `map_mem_plus` obligation to discharge, and the
universal property being transported is about ring homomorphisms rather than pair morphisms. The
two are siblings sharing a proof idiom, not a general lemma and its special case; a later rung
needing the pair-level statement should use `Pair.Hom.quotientLift`.

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
  characterises it. The values on the images of the constants and the variables follow from it by
  `simp`, so they get no separate lemmas.
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

Its continuity is `TauCeti.Huber.continuous_weightedEvalQuotientHom`. -/
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
  Ideal.Quotient.lift_mk 𝔞 _ _

/-- **The defining factorisation**: composing the induced map with the quotient map returns the
evaluation. With `Ideal.Quotient.ringHom_ext` this is what pins the induced map down. -/
@[simp]
theorem weightedEvalQuotientHom_comp_mk :
    (weightedEvalQuotientHom hT hφ hb h𝔞).comp (Ideal.Quotient.mk 𝔞) =
      weightedEvalHom hT hφ hb :=
  Ideal.Quotient.lift_comp_mk 𝔞 _ _

/-- **The induced map is continuous.** -/
theorem continuous_weightedEvalQuotientHom :
    Continuous (weightedEvalQuotientHom hT hφ hb h𝔞) :=
  Ideal.Quotient.continuous_lift 𝔞 (continuous_weightedEvalHom hT hφ hb) _

/-- **The universal property of `A⟨X⟩_T`, read on the quotient.** When `𝔞` lies in the kernel of
the evaluation, there is exactly one continuous ring homomorphism `A⟨X⟩_T ⧸ 𝔞 →+* B` taking the
prescribed values on the images of the constants and of the variables.

The witness is `TauCeti.Huber.weightedEvalQuotientHom`, so a consumer holding a continuous
homomorphism with those values gets to identify it as that map. -/
theorem existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring
    (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ T b)
    {𝔞 : Ideal (weightedRestrictedSubring T hT)}
    (h𝔞 : 𝔞 ≤ RingHom.ker (weightedEvalHom hT hφ hb)) :
    ∃! ψ : weightedRestrictedSubring T hT ⧸ 𝔞 →+* B, Continuous ψ ∧
      (∀ a, ψ (Ideal.Quotient.mk 𝔞 (weightedC T hT a)) = φ a) ∧
      ∀ i, ψ (Ideal.Quotient.mk 𝔞 (weightedX T hT i)) = b i :=
  ⟨weightedEvalQuotientHom hT hφ hb h𝔞, ⟨continuous_weightedEvalQuotientHom,
      -- the two prescribed values are the evaluation's own, read through the quotient
      fun a ↦ by simp, fun i ↦ by simp⟩,
    -- A competitor composed with the quotient map is a continuous homomorphism out of `A⟨X⟩_T`
    -- with the same values on the generators, so it is the evaluation; and a homomorphism out of
    -- a quotient is determined by that composite.
    fun _ ⟨hψ, hC, hX⟩ ↦ Ideal.Quotient.ringHom_ext <| by
      rw [weightedEvalQuotientHom_comp_mk]
      exact weightedRestrictedSubring_ringHom_ext_of_continuous hT
        (hψ.comp continuous_quot_mk) (continuous_weightedEvalHom hT hφ hb)
        (fun a ↦ (hC a).trans (weightedEvalHom_weightedC hT hφ hb a).symm)
        fun i ↦ (hX i).trans (weightedEvalHom_weightedX hT hφ hb i).symm⟩

end TauCeti.Huber

end
