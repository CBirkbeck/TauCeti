/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Commutators in associative rings

This file records identities for moving elements past powers when their ring commutator is a
scalar multiple of one of the elements, or is central for the two elements it is built from.

## Main results

* `TauCeti.Associative.mul_pow_eq_pow_mul_add_zsmul`: moving an element past a power of an
  integer-eigenvector for its commutator.
* `TauCeti.Associative.mul_pow_eq_pow_mul_add_intCast`: the same identity in shifted-factor form.
* `TauCeti.Associative.pow_succ_mul_eq_mul_pow_succ_add_nsmul`: moving an element past a power of
  another releases that many copies of a central commutator.
* `TauCeti.Associative.pow_mul_pow_succ_eq_zero_of_pow_succ_mul_pow_eq_zero`: extracting one such
  copy trades a power of the nilpotent element for a power of the commutator.
* `TauCeti.Associative.isNilpotent_of_commutator_eq`: a commutator commuting with both of its
  arguments is nilpotent as soon as one of them is.
* `TauCeti.Associative.isNilpotent_of_commutator_eq_nsmul`: the same conclusion when the
  commutator is a nonzero natural multiple of the element.
-/

public section

namespace TauCeti.Associative

variable {A : Type*} [Ring A] {x y : A} {c : ℤ}

/-- If `y` has integer eigenvalue `c` for commutation with `x`, then moving `x` past `yⁿ`
adds `n * c` copies of `yⁿ`. -/
theorem mul_pow_eq_pow_mul_add_zsmul (hxy : x * y - y * x = c • y) (n : ℕ) :
    x * y ^ n = y ^ n * x + ((n : ℤ) * c) • y ^ n := by
  have hy : x * y = y * x + c • y := by
    rw [← hxy]
    abel
  induction n with
  | zero => simp
  | succ n ih =>
    calc x * y ^ (n + 1) = x * y ^ n * y := by rw [pow_succ, ← mul_assoc]
      _ = (y ^ n * x + ((n : ℤ) * c) • y ^ n) * y := by rw [ih]
      _ = y ^ n * (x * y) + ((n : ℤ) * c) • y ^ (n + 1) := by
          rw [add_mul, mul_assoc, smul_mul_assoc, ← pow_succ]
      _ = y ^ n * (y * x + c • y) + ((n : ℤ) * c) • y ^ (n + 1) := by rw [hy]
      _ = y ^ (n + 1) * x + (c + (n : ℤ) * c) • y ^ (n + 1) := by
          rw [mul_add, ← mul_assoc, ← pow_succ, mul_smul_comm, ← pow_succ, add_assoc, ← add_smul]
      _ = y ^ (n + 1) * x + (((n + 1 : ℕ) : ℤ) * c) • y ^ (n + 1) := by
          push_cast
          ring_nf

/-- The shifted-factor form of `mul_pow_eq_pow_mul_add_zsmul`. -/
theorem mul_pow_eq_pow_mul_add_intCast (hxy : x * y - y * x = c • y) (n : ℕ) :
    x * y ^ n = y ^ n * (x + (c : A) * (n : A)) := by
  rw [mul_pow_eq_pow_mul_add_zsmul hxy, zsmul_eq_mul', mul_add, Int.cast_mul,
    Int.cast_natCast, (Nat.cast_commute n (c : A)).eq]

section CentralCommutator

variable {A : Type*} [Ring A] [Algebra ℚ A] {x y z : A}

omit [Algebra ℚ A] in
/-- **Moving `y` past a power of `x` releases that many copies of a central commutator.** If
`x * y = y * x + z` and `z` commutes with `x`, then `x ^ (m + 1) * y` is `y * x ^ (m + 1)` plus
`m + 1` copies of `z * x ^ m`.

The section's `[Algebra ℚ A]` is omitted: the identity holds over any ring. -/
theorem pow_succ_mul_eq_mul_pow_succ_add_nsmul (hxy : x * y = y * x + z) (hxz : Commute x z)
    (m : ℕ) : x ^ (m + 1) * y = y * x ^ (m + 1) + (m + 1) • (z * x ^ m) := by
  induction m with
  | zero => simpa using hxy
  | succ m ih =>
    have hzx : x * (z * x ^ m) = z * x ^ (m + 1) := by
      rw [← mul_assoc, hxz.eq, mul_assoc, ← pow_succ']
    calc x ^ (m + 1 + 1) * y = x * (x ^ (m + 1) * y) := by rw [← mul_assoc, ← pow_succ']
      _ = x * y * x ^ (m + 1) + (m + 1) • (z * x ^ (m + 1)) := by
          rw [ih, mul_add, ← mul_assoc, mul_smul_comm, hzx]
      _ = y * x ^ (m + 1 + 1) + (z * x ^ (m + 1) + (m + 1) • (z * x ^ (m + 1))) := by
          rw [hxy, add_mul, mul_assoc, ← pow_succ', add_assoc]
      _ = y * x ^ (m + 1 + 1) + (m + 1 + 1) • (z * x ^ (m + 1)) := by
          rw [← succ_nsmul']

/-- **Extracting one copy of a central commutator trades a power of `x` for a power of `z`.** If
`x ^ (m + 1)` annihilates `z ^ k` on the left, then `x ^ m` annihilates `z ^ (k + 1)`. -/
theorem pow_mul_pow_succ_eq_zero_of_pow_succ_mul_pow_eq_zero (hxy : x * y = y * x + z)
    (hxz : Commute x z) (hyz : Commute y z) {m k : ℕ} (h : x ^ (m + 1) * z ^ k = 0) :
    x ^ m * z ^ (k + 1) = 0 := by
  -- Pushing `y` to the right kills the product outright.
  have hA : x ^ (m + 1) * y * z ^ k = 0 := by
    rw [mul_assoc, ← (hyz.symm.pow_left k).eq, ← mul_assoc, h, zero_mul]
  -- Pushing it to the left leaves the released copies of `z`.
  have hB : x ^ (m + 1) * y * z ^ k = (m + 1) • (x ^ m * z ^ (k + 1)) := by
    rw [pow_succ_mul_eq_mul_pow_succ_add_nsmul hxy hxz m, add_mul, mul_assoc, h, mul_zero,
      zero_add, smul_mul_assoc, (hxz.symm.pow_right m).eq, mul_assoc, ← pow_succ']
  have hkey : ((m + 1 : ℕ) : ℚ) • (x ^ m * z ^ (k + 1)) = 0 := by
    rw [Nat.cast_smul_eq_nsmul ℚ, ← hB]
    exact hA
  have hc : (((m + 1 : ℕ) : ℚ))⁻¹ • (((m + 1 : ℕ) : ℚ) • (x ^ m * z ^ (k + 1))) = 0 := by
    rw [hkey, smul_zero]
  rwa [inv_smul_smul₀ (Nat.cast_ne_zero.mpr m.succ_ne_zero)] at hc

/-- **Nilpotency of a central commutator.** If `x * y = y * x + z` with `z` commuting with both `x`
and `y`, then `z` is nilpotent as soon as `x` is, with the same nilpotency exponent. -/
theorem isNilpotent_of_commutator_eq (hxy : x * y = y * x + z) (hxz : Commute x z)
    (hyz : Commute y z) (hx : IsNilpotent x) : IsNilpotent z := by
  obtain ⟨n, hn⟩ := hx
  -- Peel the powers of `x` off one at a time, trading each for a power of `z`.
  have hpeel : ∀ k ≤ n, x ^ (n - k) * z ^ k = 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using hn
    | succ k ih =>
      intro hk
      have heq : n - k = n - (k + 1) + 1 := by omega
      exact pow_mul_pow_succ_eq_zero_of_pow_succ_mul_pow_eq_zero hxy hxz hyz
        (by rw [← heq]; exact ih (by omega))
  exact ⟨n, by simpa using hpeel n le_rfl⟩

/-- If `x * y = y * x + n • z` for a nonzero natural number `n`, with `z` commuting with `x`
and `y`, then `z` is nilpotent whenever `x` is. -/
theorem isNilpotent_of_commutator_eq_nsmul {n : ℕ} (hn : n ≠ 0)
    (hxy : x * y = y * x + n • z) (hxz : Commute x z) (hyz : Commute y z)
    (hx : IsNilpotent x) : IsNilpotent z := by
  have hnQ : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnil := (isNilpotent_of_commutator_eq hxy (hxz.smul_right n)
    (hyz.smul_right n) hx).smul ((n : ℚ)⁻¹)
  simpa only [← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ hnQ] using hnil

end CentralCommutator

end TauCeti.Associative
