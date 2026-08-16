/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Applying `ZMod.finEquiv`

Mathlib defines `ZMod.finEquiv : Fin n ≃+* ZMod n` for `[NeZero n]` and states nothing about
applying it. This file supplies the evaluation rule, so that an argument indexed by `Fin n` can be
carried into `ZMod n` arithmetic.

## Main results

* `ZMod.finEquiv_apply`: `ZMod.finEquiv n j` is the natural cast of `j.val`.
* `ZMod.val_finEquiv_symm`: the `Fin n` representative it produces has that element as its `val`.
-/

public section

namespace ZMod

/-- **Applying `ZMod.finEquiv` is the natural cast.** Mathlib defines `finEquiv` and states no
evaluation rule for it, so without this a `Fin n`-indexed statement cannot meet `ZMod n`
arithmetic.

The proof is a definitional reduction, and deliberately so. `ZMod.finEquiv` is `RingEquiv.refl` on
the successor branch and `ZMod (k + 1)` unfolds to `Fin (k + 1)`, so the two sides are the same
term once those are unfolded. `simp` cannot do it: `Fin.cast_val_eq_self` is stated at `Fin n`
while this goal's cast lands in `ZMod (k + 1)`, and although the types agree after unfolding, the
`NatCast` instances are syntactically different — `simp` reports the lemma unused. `exact`
succeeds because it checks up to definitional equality. -/
@[simp]
lemma finEquiv_apply {n : ℕ} [NeZero n] (j : Fin n) :
    (ZMod.finEquiv n) j = ((j : ℕ) : ZMod n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  exact (Fin.cast_val_eq_self j).symm

/-- The `Fin n` representative `ZMod.finEquiv` produces is the element's `val`. The companion of
`finEquiv_apply` in the other direction, and the form needed to index by `Fin n` an element
obtained by solving in `ZMod n`. -/
@[simp]
lemma val_finEquiv_symm {n : ℕ} [NeZero n] (z : ZMod n) :
    (((ZMod.finEquiv n).symm z : Fin n) : ℕ) = z.val := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  rfl

end ZMod
