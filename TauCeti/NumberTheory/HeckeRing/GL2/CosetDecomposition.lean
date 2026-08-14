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
* `HeckeRing.GL2.upperTriRep`: the `b`-th representative `!![1, b; 0, p]`.

## Main results

* `HeckeRing.GL2.upperTriEntriesEquiv_apply`, `upperTriEntriesEquiv_symm_apply_default`: the
  equivalence reads off, and installs, the coordinate at the unique index pair.
* `HeckeRing.GL2.upperTriEntriesEquivFin_val`, `upperTriEntriesEquivFin_symm_val`: the same for
  `a = ![1, p]`, as an identity of natural numbers — the two fibres `Fin (![1, p] 1 / ![1, p] 0)`
  and `Fin p` are definitionally but not syntactically equal.
* `HeckeRing.GL2.upperTriRep_apply_one_zero`: the representatives are upper triangular — the
  hypothesis mathlib's `IsBoundedAtImInfty.slash` asks for.
* `HeckeRing.GL2.det_upperTriRep_pos`: they have determinant `p > 0`, which is what lets scalars
  pass through a slash by them without the `σ` twist.
-/

public section

namespace HeckeRing.GL2

open HeckeRing.GLn

variable (p : ℕ)

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
`finCongr` rather than a rewrite. -/
@[expose]
def upperTriEntriesEquiv (a : Fin 2 → ℕ) : UpperTriEntries 2 a ≃ Fin (a 1 / a 0) :=
  Equiv.piUnique _

@[simp]
lemma upperTriEntriesEquiv_apply {a : Fin 2 → ℕ} (B : UpperTriEntries 2 a) :
    upperTriEntriesEquiv a B = B default := rfl

@[simp]
lemma upperTriEntriesEquiv_symm_apply_default {a : Fin 2 → ℕ} (b : Fin (a 1 / a 0)) :
    (upperTriEntriesEquiv a).symm b default = b := rfl

/-- **The classical index of the upper-triangular representatives.** For `a = ![1, p]` the entry
assignments are just the offsets `b ∈ Fin p`, so `upperTriGL` at these entries runs over the
familiar `!![1, b; 0, p]`. -/
@[expose]
def upperTriEntriesEquivFin (p : ℕ) : UpperTriEntries 2 ![1, p] ≃ Fin p :=
  (upperTriEntriesEquiv _).trans (finCongr (by simp))

@[simp]
lemma upperTriEntriesEquivFin_val {p : ℕ} (B : UpperTriEntries 2 ![1, p]) :
    (upperTriEntriesEquivFin p B : ℕ) = (B default : ℕ) := rfl

@[simp]
lemma upperTriEntriesEquivFin_symm_val {p : ℕ} (b : Fin p) :
    (((upperTriEntriesEquivFin p).symm b default : ℕ)) = (b : ℕ) := rfl

/-- The `b`-th upper-triangular representative `!![1, b; 0, p]`, as an element of this
repository's general-`n` family at `a = ![1, p]`. -/
noncomputable def upperTriRep (b : Fin p) : GL (Fin 2) ℚ :=
  upperTriGL ((upperTriEntriesEquivFin p).symm b)

lemma upperTriRep_def (b : Fin p) :
    upperTriRep p b = upperTriGL ((upperTriEntriesEquivFin p).symm b) := (rfl)

/-- **The representatives are upper triangular** — the hypothesis mathlib's
`IsBoundedAtImInfty.slash` asks for. At `n = 2` this is the `(1, 0)` entry of
`upperTriGL_apply_eq_zero_of_lt`. -/
@[simp] lemma upperTriRep_apply_one_zero (b : Fin p) :
    (↑(upperTriRep p b) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 :=
  upperTriGL_apply_eq_zero_of_lt (fun i ↦ by fin_cases i <;> simp [b.pos]) _ (by decide)

/-- The representatives have positive determinant: `det !![1, b; 0, p] = p > 0`. -/
lemma det_upperTriRep_pos (b : Fin p) :
    0 < (↑(upperTriRep p b) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [upperTriRep_def, upperTriGL_coe (fun i ↦ by fin_cases i <;> simp [b.pos]),
    Matrix.det_mul, Matrix.det_diagonal]
  simp [Matrix.det_fin_two, Matrix.map_apply, Fin.prod_univ_two, b.pos]

end HeckeRing.GL2

end
