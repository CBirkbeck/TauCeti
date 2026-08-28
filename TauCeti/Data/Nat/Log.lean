/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Common

/-!
# The base-`b` logarithm grows by at most one, and is sublinear

Two facts about `Nat.log` that Mathlib does not carry. Mathlib has the exact criterion for when
the logarithm jumps at a successor (`Nat.log_lt_log_succ_iff`), but not the resulting one-step
bound, and it has no asymptotic statement at all.

## Main results

* `Nat.log_succ_le` : `Nat.log b (n + 1) ≤ Nat.log b n + 1`.
* `tendsto_sub_log_atTop` : `n - Nat.log p n → ∞` for `1 < p`, i.e. the logarithm is sublinear.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`,
  `EllipticCurves/Mathlib/Chabauty/PadicValNat.lean`. The proofs are that file's, with its `lia`
  calls replaced by `omega`, which is this repository's idiom.
-/

public section

open Filter

/-- `Nat.log` increases by at most one when its argument does. -/
theorem Nat.log_succ_le (b n : ℕ) : Nat.log b (n + 1) ≤ Nat.log b n + 1 := by
  by_cases hb : 1 < b
  · rcases Nat.eq_zero_or_pos (Nat.log b (n + 1)) with h0 | hL
    · omega
    set L := Nat.log b (n + 1) with hLdef
    have hpL : b ^ L ≤ n + 1 := Nat.pow_log_le_self b (Nat.succ_ne_zero n)
    have hone : 1 ≤ b ^ (L - 1) := Nat.one_le_pow _ _ (by omega)
    have h2 : 2 * b ^ (L - 1) ≤ b ^ L := by
      have he : b ^ L = b ^ (L - 1) * b := by rw [← Nat.pow_succ]; congr 1; omega
      rw [he, Nat.mul_comm (b ^ (L - 1)) b]
      exact Nat.mul_le_mul_right _ hb
    have h4 : b ^ (L - 1) ≤ n := by omega
    have := Nat.le_log_of_pow_le hb h4
    omega
  · simp [Nat.log_of_left_le_one (by omega : b ≤ 1)]

/-- `n - Nat.log p n → ∞`: the base-`p` logarithm is sublinear. -/
theorem tendsto_sub_log_atTop {p : ℕ} (hp : 1 < p) :
    Tendsto (fun n ↦ n - Nat.log p n) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone
  · refine monotone_nat_of_le_succ fun n ↦ ?_
    have h1 : Nat.log p (n + 1) ≤ Nat.log p n + 1 := Nat.log_succ_le p n
    have h2 : Nat.log p n ≤ Nat.log p (n + 1) := Nat.log_mono_right (Nat.le_succ n)
    omega
  · intro B
    refine ⟨p ^ (B + 1), ?_⟩
    rw [Nat.log_pow hp]
    have hk : B + 1 ≤ 2 ^ B := Nat.lt_two_pow_self
    have h2 : 2 ^ (B + 1) ≤ p ^ (B + 1) := Nat.pow_le_pow_left (by omega) (B + 1)
    have h3 : 2 * (B + 1) ≤ 2 ^ (B + 1) := by rw [Nat.pow_succ]; omega
    omega

end
