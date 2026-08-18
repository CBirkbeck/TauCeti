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

/-- **Applying `ZMod.finEquiv` is the natural cast.** `ZMod.finEquiv n j` is the image of `j.val`
under `Nat.cast`. Mathlib defines `finEquiv` and states no evaluation rule for it, so without this
a `Fin n`-indexed statement cannot meet `ZMod n` arithmetic. -/
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
