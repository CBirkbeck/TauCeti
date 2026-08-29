/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

/-!
# Stabilisation of the powers of an ideal killed by a unit-like element

If some `1 + i` with `i ∈ I` annihilates `I ^ n`, then the powers of `I` stabilise at `n`:
`I ^ k = I ^ n` for every `k ≥ n`.

The mechanism is that `(1 + i) * x = 0` rewrites `x` as `-(x * i)`, which moves it one power
deeper, so `I ^ n` is contained in `I ^ (n + 1)` and the two agree.

## Main results

* `TauCeti.Ideal.pow_eq_pow_succ_of_forall_one_add_mul_eq_zero`: `I ^ n = I ^ (n + 1)`.
* `TauCeti.Ideal.pow_eq_pow_of_le_of_pow_eq_pow_succ`: `I ^ k = I ^ n` for all `k ≥ n`.
-/

public section

namespace TauCeti.Ideal

variable {B : Type*} [CommRing B] {I : _root_.Ideal B}

/-- **One power of `I` absorbs the next**, when some `1 + i` with `i ∈ I` annihilates `I ^ n`:
for `x ∈ I ^ n` the relation `(1 + i) * x = 0` says `x = -(x * i)`, and `x * i` lies in
`I ^ n * I = I ^ (n + 1)`. -/
theorem pow_eq_pow_succ_of_forall_one_add_mul_eq_zero {i : B} (hi : i ∈ I) {n : ℕ}
    (h : ∀ x ∈ I ^ n, (1 + i) * x = 0) : I ^ n = I ^ (n + 1) := by
  refine le_antisymm (fun x hx ↦ ?_) (_root_.Ideal.pow_le_pow_right n.le_succ)
  have hx0 : (1 + i) * x = 0 := h x hx
  have hsum : x + x * i = 0 := by rw [← hx0]; ring
  have hxeq : x = -(x * i) := eq_neg_of_add_eq_zero_left hsum
  rw [hxeq, pow_succ]
  exact neg_mem (_root_.Ideal.mul_mem_mul hx hi)

/-- **The powers stabilise from `n` on**, once `I ^ n = I ^ (n + 1)`. -/
theorem pow_eq_pow_of_le_of_pow_eq_pow_succ {n : ℕ} (hstab : I ^ n = I ^ (n + 1)) :
    ∀ {k : ℕ}, n ≤ k → I ^ k = I ^ n := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [pow_succ, ih, ← pow_succ, ← hstab]

end TauCeti.Ideal
