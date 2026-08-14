/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.CosetDecomposition

/-!
# The upper-triangular entry assignments at `n = 2`

`GLn/CosetDecomposition.lean` indexes the upper-triangular coset representatives by the bounded
entry assignments `UpperTriEntries n a`, a dependent function on the ordered index pairs
`{ij : Fin n × Fin n // ij.1 < ij.2}`. At `n = 2` there is exactly one such pair, `(0, 1)`, so an
assignment carries a single coordinate and `UpperTriEntries 2 a` is just `Fin (a 1 / a 0)`.

This file records that identification, and its specialisation to `a = ![1, p]`, where the
coordinate is an offset `b ∈ Fin p` and `upperTriGL` runs over the classical `!![1, b; 0, p]`.
It is the adapter between the general-`n` decomposition and the classical `T_p` bookkeeping,
which sums over `b` directly: a sum over `UpperTriEntries 2 ![1, p]` transfers along this
equivalence rather than being restated.

Nothing here involves a level or a congruence subgroup; the level-`N` membership statements for
these representatives are in `GL2/UpperTriangularDelta0.lean`.

## Main definitions

* `HeckeRing.GL2.uniqueIndexPair`: `(0, 1)` is the only ordered index pair at `n = 2`.
* `HeckeRing.GL2.upperTriEntriesEquiv`: `UpperTriEntries 2 a ≃ Fin (a 1 / a 0)`, for an
  arbitrary tuple `a`.
* `HeckeRing.GL2.upperTriEntriesEquivFin`: its specialisation `UpperTriEntries 2 ![1, p] ≃ Fin p`.

## Main results

* `HeckeRing.GL2.upperTriEntriesEquiv_apply`, `upperTriEntriesEquiv_symm_apply_default`: the
  equivalence reads off, and installs, the coordinate at the unique index pair.
* `HeckeRing.GL2.upperTriEntriesEquivFin_val`, `upperTriEntriesEquivFin_symm_val`: the same for
  `a = ![1, p]`, as an identity of natural numbers — the two fibres `Fin (![1, p] 1 / ![1, p] 0)`
  and `Fin p` are definitionally but not syntactically equal.

## Provenance

No code is ported: the equivalence is a fact about this repository's own `UpperTriEntries`. The
"classical `T_p` bookkeeping" it adapts to is that of the AINTLIB `LeanModularForms` project
(Chris Birkbeck, Apache-2.0), `LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, whose `heckeT_p_ut` sums over `b ∈ Finset.range p`
and whose `T_p_upper p _ b = !![1, b; 0, p]` is `upperTriGL` at `n = 2`, `a = ![1, p]`. This file
exists so that such a sum transfers onto the existing general-`n` decomposition instead of
restating the index.
-/

public section

namespace HeckeRing.GL2

open HeckeRing.GLn

/-- At `n = 2` there is exactly one ordered index pair, `(0, 1)`, so `UpperTriEntries` is a
function on a one-element type. -/
instance uniqueIndexPair : Unique {ij : Fin 2 × Fin 2 // ij.1 < ij.2} where
  default := ⟨(0, 1), by decide⟩
  uniq := by rintro ⟨ij, h⟩; apply Subtype.ext; revert h; revert ij; decide

@[simp]
lemma default_indexPair_val : (default : {ij : Fin 2 × Fin 2 // ij.1 < ij.2}).val = (0, 1) := rfl

/-- **An entry assignment at `n = 2` is a single coordinate.** `UpperTriEntries 2 a` is a
dependent function on the ordered index pairs, and by `uniqueIndexPair` there is only the pair
`(0, 1)`; the fibre over it is `Fin (a 1 / a 0)`.

The stated fibre `Fin (a 1 / a 0)` is the fibre `Fin (a default.val.2 / a default.val.1)` that
`Equiv.piUnique` produces: `default` is *definitionally* `⟨(0, 1), _⟩`, since that is the field
of `uniqueIndexPair`. It is not syntactically that, which is why the specialisation below needs
`finCongr` rather than a rewrite.

`@[expose]` is load-bearing, not decoration: the four characteristic lemmas below are proved by
`rfl`, and without it the compiler rejects them with "this theorem is exported from the current
module, [so] all definitions that need to be unfolded to prove this theorem must be exposed".
Removing it does not trade one API for another — it leaves the equivalence with no usable
characteristic equations at all. -/
@[expose]
def upperTriEntriesEquiv (a : Fin 2 → ℕ) : UpperTriEntries 2 a ≃ Fin (a 1 / a 0) :=
  Equiv.piUnique _

/-- The equivalence reads off the coordinate at the unique index pair. -/
@[simp]
lemma upperTriEntriesEquiv_apply {a : Fin 2 → ℕ} (B : UpperTriEntries 2 a) :
    upperTriEntriesEquiv a B = B default := rfl

/-- Its inverse installs a given coordinate at the unique index pair. -/
@[simp]
lemma upperTriEntriesEquiv_symm_apply_default {a : Fin 2 → ℕ} (b : Fin (a 1 / a 0)) :
    (upperTriEntriesEquiv a).symm b default = b := rfl

/-- **The classical index of the upper-triangular representatives.** For `a = ![1, p]` the entry
assignments are just the offsets `b ∈ Fin p`, so `upperTriGL` at these entries runs over the
familiar `!![1, b; 0, p]`. -/
@[expose]
def upperTriEntriesEquivFin (p : ℕ) : UpperTriEntries 2 ![1, p] ≃ Fin p :=
  (upperTriEntriesEquiv _).trans (finCongr (by simp))

/-- At `a = ![1, p]` the offset read off is the coordinate, as natural numbers: the fibres
`Fin (![1, p] 1 / ![1, p] 0)` and `Fin p` are definitionally but not syntactically equal. -/
@[simp]
lemma upperTriEntriesEquivFin_val {p : ℕ} (B : UpperTriEntries 2 ![1, p]) :
    (upperTriEntriesEquivFin p B : ℕ) = (B default : ℕ) := rfl

/-- At `a = ![1, p]` the coordinate installed is the offset, as natural numbers. -/
@[simp]
lemma upperTriEntriesEquivFin_symm_val {p : ℕ} (b : Fin p) :
    (((upperTriEntriesEquivFin p).symm b default : ℕ)) = (b : ℕ) := rfl

end HeckeRing.GL2

end
