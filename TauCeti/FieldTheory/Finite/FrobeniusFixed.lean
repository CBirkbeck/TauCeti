/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The fixed points of the `q`-power map in an extension of a finite field

For a finite field `K` with `q` elements and any field extension `L`, an element of `L` is fixed by
the `q`-power map exactly when it comes from `K`:

`a ^ q = a ↔ a ∈ Set.range (algebraMap K L)`.

## Main results

* `TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap`: the criterion above.

Mathlib has the easy direction (`FiniteField.pow_card`) but not the equivalence.
`IsGalois.mem_range_algebraMap_iff_fixed` characterises the base field of a Galois extension by
being fixed, but it needs `[FiniteDimensional F E]` and quantifies over the whole Galois group
rather than the single `q`-power map.

Nothing is assumed of `L` beyond being a field extension: in particular it need not be
algebraically closed, which is the only case the source states.

This is the field-theoretic input to the Hasse route of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 3 ("elliptic curves over finite fields — the Hasse
bound"), whose zeta-function bullet fixes "the **fixed points of `π_qⁿ` on `E(𝔽̄_q)`**" as the model
of record for `E(𝔽_qⁿ)`: this is that identification one level down, on coordinates rather than
points.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`),
`HasseWeil/Curves/FrobeniusFixedLocus.lean`, declaration `frobenius_fixed_iff_mem_baseField`.

Changes from the source. It is stated there only for `L = AlgebraicClosure K`; here `L` is an
arbitrary field extension, since nothing in the argument uses algebraic closedness. The source
builds the root-set transport by hand, through a separability argument and a finset count; here
that is Mathlib's `Splits.image_rootSet` applied to `FiniteField.isSplittingField_sub`. And the
source's other public theorem is stated in terms of its own `private` finsets, so it cannot be
applied from outside; it is not reproduced. Nine declarations become one.
-/

public section

open Polynomial

namespace TauCeti

namespace FiniteField

/-- **An element of a field extension of a finite field is fixed by the `q`-power map exactly when
it comes from the base field**, where `q` is the cardinality of the base. -/
theorem pow_card_eq_self_iff_mem_range_algebraMap {K L : Type*} [Field K] [Fintype K] [Field L]
    [Algebra K L] (a : L) : a ^ Fintype.card K = a ↔ a ∈ Set.range (algebraMap K L) := by
  classical
  -- `X ^ q - X` splits over `K` with every element a root, and `Splits.image_rootSet`
  -- transports that root set along `K → L`
  have hne : (X ^ Fintype.card K - X : K[X]) ≠ 0 :=
    _root_.FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
  have hsplits : ((X ^ Fintype.card K - X : K[X]).map (algebraMap K K)).Splits :=
    IsSplittingField.splits (L := K) (X ^ Fintype.card K - X)
  have himg := hsplits.image_rootSet (Algebra.ofId K L)
  have hK : (X ^ Fintype.card K - X : K[X]).rootSet K = Set.univ := by
    ext b
    simp [mem_rootSet_of_ne hne, _root_.FiniteField.pow_card]
  rw [Set.ext_iff] at himg
  have := himg a
  simp only [hK, Set.image_univ, Algebra.ofId_apply, mem_rootSet_of_ne hne, aeval_def,
    eval₂_sub, eval₂_X_pow, eval₂_X, sub_eq_zero] at this
  exact this.symm

end FiniteField

end TauCeti
