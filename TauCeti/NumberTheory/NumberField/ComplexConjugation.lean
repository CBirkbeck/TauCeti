/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# The canonical element at a ramified real place

Let `L / K` be a Galois extension and `w` a complex place of `L` lying above a real place of `K`,
that is a place with `w.IsRamified K`. Exactly one nonidentity automorphism of `L / K` conjugates
the embedding attached to `w`, and this file names it `complexConjugationAt K w hw`.

The place is part of the input. In a general Galois extension there is no place-independent
conjugation element: Mathlib's `IsCMField.complexConj` picks one by choosing an embedding once
and for all, which is available only for a CM field. Indexing by the place is what makes the
element canonical in general, and the indexing is exactly what the API below records.

Everything here rests on Mathlib's embedding-level theory of `ComplexEmbedding.IsConj`, which
already supplies existence at a ramified place (`exists_isConj_of_isRamified`), uniqueness
(`ComplexEmbedding.IsConj.ext`), order two, and the description of the stabilizer. This file
transports that theory to the place `w` itself and gives the resulting element a name; it does
not restate any of it.

⚠ This element is not a Frobenius. At an infinite place the local Galois group is `Gal(ℂ/ℝ)`:
there is no residue field, and no congruence `σ x ≡ x ^ q`.

## Main definitions

* `TauCeti.NumberField.complexConjugationAt`: the conjugation attached to a ramified place.

## Main results

* `TauCeti.NumberField.isConj_complexConjugationAt`: it conjugates `w.embedding`.
* `TauCeti.NumberField.eq_complexConjugationAt`: it is the only automorphism that does, so the
  name is justified.
* `TauCeti.NumberField.complexConjugationAt_ne_one` and
  `TauCeti.NumberField.orderOf_complexConjugationAt`: it is nontrivial, of order two.
* `TauCeti.NumberField.coe_stabilizer_eq`: the stabilizer of `w` is exactly `{1, c}`, and
  `TauCeti.NumberField.complexConjugationAt_mem_stabilizer` records the membership.

Deferred to follow-ups, one topic each: conjugacy covariance
`complexConjugationAt (σ • w) = σ * complexConjugationAt w * σ⁻¹`, which needs the comparison of
`(σ • w).embedding` with `w.embedding`; restriction in a normal tower, with its two branches
according as the induced place stays complex or becomes real; and the CM specialization
identifying these elements with `IsCMField.complexConj`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §3.
-/

public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

variable (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L] [IsGalois K L]

/-- **The canonical conjugation at a ramified place.** For `w` a place of `L` ramified over `K`,
this is the unique nonidentity element of `Gal(L/K)` conjugating the embedding of `w`.

The hypothesis `hw` is data of the statement, not decoration: at an unramified place the only
automorphism conjugating the embedding is the identity, and there is nothing to name. -/
noncomputable def complexConjugationAt (w : InfinitePlace L) (hw : w.IsRamified K) : L ≃ₐ[K] L :=
  (exists_isConj_of_isRamified (k := K) (φ := w.embedding) (by rwa [mk_embedding])).choose

/-- `complexConjugationAt K w hw` conjugates the embedding attached to `w`. -/
theorem isConj_complexConjugationAt (w : InfinitePlace L) (hw : w.IsRamified K) :
    ComplexEmbedding.IsConj w.embedding (complexConjugationAt K w hw) :=
  (exists_isConj_of_isRamified (k := K) (φ := w.embedding) (by rwa [mk_embedding])).choose_spec

/-- **Uniqueness.** Any automorphism conjugating the embedding of `w` is `complexConjugationAt`,
so the definition does not depend on the choice made to produce it. -/
theorem eq_complexConjugationAt {w : InfinitePlace L} (hw : w.IsRamified K) {σ : L ≃ₐ[K] L}
    (hσ : ComplexEmbedding.IsConj w.embedding σ) : σ = complexConjugationAt K w hw :=
  hσ.ext (isConj_complexConjugationAt K w hw)

/-- The conjugation at a ramified place is not the identity: were it, the place would be
unramified. -/
theorem complexConjugationAt_ne_one (w : InfinitePlace L) (hw : w.IsRamified K) :
    complexConjugationAt K w hw ≠ 1 := by
  rw [ne_eq, ← (isConj_complexConjugationAt K w hw).isUnramified_mk_iff, mk_embedding]
  exact hw

/-- **The conjugation at a ramified place has order two**, matching `Gal(ℂ/ℝ)`. -/
theorem orderOf_complexConjugationAt (w : InfinitePlace L) (hw : w.IsRamified K) :
    orderOf (complexConjugationAt K w hw) = 2 :=
  ComplexEmbedding.orderOf_isConj_two_of_ne_one (isConj_complexConjugationAt K w hw)
    (complexConjugationAt_ne_one K w hw)

/-- **The stabilizer of a ramified place is `{1, c}`**, for `c` the conjugation at that place. -/
theorem coe_stabilizer_eq (w : InfinitePlace L) (hw : w.IsRamified K) :
    (MulAction.stabilizer (L ≃ₐ[K] L) w : Set (L ≃ₐ[K] L)) =
      {1, complexConjugationAt K w hw} := by
  have h := (isConj_complexConjugationAt K w hw).coe_stabilizer_mk
  rwa [mk_embedding] at h

/-- The conjugation at `w` fixes `w`. -/
theorem complexConjugationAt_mem_stabilizer (w : InfinitePlace L) (hw : w.IsRamified K) :
    complexConjugationAt K w hw ∈ MulAction.stabilizer (L ≃ₐ[K] L) w := by
  rw [← SetLike.mem_coe, coe_stabilizer_eq K w hw]
  exact Set.mem_insert_of_mem _ rfl

end TauCeti.NumberField
