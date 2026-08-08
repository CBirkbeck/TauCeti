/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# The fixed points of the `q`-power map in an extension of a finite field

For a finite field `K` with `q` elements and any field extension `L`, an element of `L` is fixed by
the `q`-power map exactly when it comes from `K`:

`a ^ q = a ↔ a ∈ Set.range (algebraMap K L)`.

## Main results

* `TauCeti.FiniteField.pow_card_eq_self_iff_mem_range`: the criterion above.

Mathlib has the easy direction (`FiniteField.pow_card`) but not the equivalence.
`IsGalois.mem_range_algebraMap_iff_fixed` characterises the base field of a Galois extension by
being fixed, but it needs `[FiniteDimensional F E]` and quantifies over the whole Galois group
rather than the single `q`-power map.

The argument is counting, and it needs nothing of `L`: the polynomial `X ^ q - X` has at most `q`
roots in any field, and the `q` images of `K` are already roots, so those are all of them. In
particular neither algebraic closedness nor separability is required — `X ^ q - X` is separable,
but that fact is not needed, because passing to the finset of roots discards multiplicity anyway.

This is the field-theoretic input to the Hasse route of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 3 ("elliptic curves over finite fields — the Hasse
bound"), whose zeta-function bullet fixes "the **fixed points of `π_qⁿ` on `E(𝔽̄_q)`**" as the model
of record for `E(𝔽_qⁿ)`: this is that identification one level down, on coordinates rather than
points.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`),
`HasseWeil/Curves/FrobeniusFixedLocus.lean`, declaration `frobenius_fixed_iff_mem_baseField`.

Two changes from the source. It is stated there only for `L = AlgebraicClosure K`; here `L` is an
arbitrary field extension, since the proof never uses algebraic closedness. And the source's
separability argument (four auxiliary lemmas establishing that the derivative of `X ^ q - X` is
`-1`) is dropped, being unnecessary for the count. What remains is one theorem rather than nine
declarations, and the source's public theorem stated in terms of its own private finsets is not
reproduced.
-/

public section

open Polynomial

namespace TauCeti

namespace FiniteField

/-- **An element of a field extension of a finite field is fixed by the `q`-power map exactly when
it comes from the base field**, where `q` is the cardinality of the base.

The `q` images of `K` are roots of `X ^ q - X`, which has at most `q` roots; so they are all of
them, and being fixed by the `q`-power map is exactly being such a root. -/
theorem pow_card_eq_self_iff_mem_range {K L : Type*} [Field K] [Fintype K] [Field L] [Algebra K L]
    (a : L) : a ^ Fintype.card K = a ↔ a ∈ Set.range (algebraMap K L) := by
  classical
  have hne : (X ^ Fintype.card K - X : L[X]) ≠ 0 :=
    _root_.FiniteField.X_pow_card_sub_X_ne_zero L Fintype.one_lt_card
  have hmem_roots : ∀ b : L,
      b ∈ (X ^ Fintype.card K - X : L[X]).roots.toFinset ↔ b ^ Fintype.card K = b := by
    intro b
    rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
    simp only [eval_sub, eval_pow, eval_X, sub_eq_zero]
  have hmem_image : ∀ b : L,
      b ∈ Finset.univ.image (algebraMap K L) ↔ b ∈ Set.range (algebraMap K L) := by
    simp [Set.mem_range, eq_comm]
  have hsub : Finset.univ.image (algebraMap K L) ⊆
      (X ^ Fintype.card K - X : L[X]).roots.toFinset := fun b hb => by
    obtain ⟨c, rfl⟩ := (hmem_image b).mp hb
    exact (hmem_roots _).mpr (by rw [← map_pow, _root_.FiniteField.pow_card])
  have hcard : (Finset.univ.image (algebraMap K L)).card = Fintype.card K := by
    rw [Finset.card_image_of_injective _ (algebraMap K L).injective, Finset.card_univ]
  have hle : (X ^ Fintype.card K - X : L[X]).roots.toFinset.card ≤ Fintype.card K :=
    calc (X ^ Fintype.card K - X : L[X]).roots.toFinset.card
        ≤ Multiset.card (X ^ Fintype.card K - X : L[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ Fintype.card K - X : L[X]).natDegree := card_roots' _
      _ = Fintype.card K :=
          _root_.FiniteField.X_pow_card_sub_X_natDegree_eq L Fintype.one_lt_card
  rw [← hmem_roots a, ← hmem_image a,
    Finset.eq_of_subset_of_card_le hsub (hcard ▸ hle)]

end FiniteField

end TauCeti
