/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Stabilization of the powers of an ideal

Two facts about when the powers of an ideal `I` become constant.

The first is general: if `I ^ (n + 1) = I ^ n`, then `I ^ k = I ^ n` for every `k ≥ n`. Nothing
about the ring beyond `Semiring` is used, and no annihilator appears.

The second is the conditional stabilization criterion: if some `i ∈ I` is such that `1 + i`
annihilates `I ^ n`, then `I ^ (n + 1) = I ^ n`, and hence the powers are constant from `n` on.
The annihilating element is a **hypothesis** here.

Finite generation of `I`, and the localization at `1 + I` that produces such an `i` in Wedhorn's
proof of Proposition 7.49(2), are deliberately **outside** this module: nothing below mentions a
localization, and no theorem here derives the annihilator. The submonoid `1 + I` is defined
because it is the natural home of that element, and because being a *submonoid* is what allows
finitely many annihilating witnesses to be combined into one.

## Main definitions

* `Ideal.oneAdd`: the submonoid `1 + I` of `B`.

## Main results

* `Ideal.pow_eq_pow_of_pow_succ_eq_pow`: `I ^ (n + 1) = I ^ n` propagates to all `k ≥ n`.
* `Ideal.pow_succ_eq_pow_of_forall_mul_eq_zero`: an `i ∈ I` whose `1 + i` annihilates `I ^ n`
  gives `I ^ (n + 1) = I ^ n`.
* `Ideal.pow_eq_pow_of_forall_mul_eq_zero`: hence `I ^ k = I ^ n` for all `k ≥ n`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], proof of Proposition 7.49(2), where the conditional
  criterion is the closing step.
-/

public section

namespace Ideal

section Semiring

variable {R : Type*} [Semiring R]

/-- Once the powers of an ideal repeat once, they are constant from that point on. -/
theorem pow_eq_pow_of_pow_succ_eq_pow {I : _root_.Ideal R} {n : ℕ} (h : I ^ (n + 1) = I ^ n)
    {k : ℕ} (hk : n ≤ k) : I ^ k = I ^ n := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ m _ ih =>
    have hstep : I ^ (m + 1) = I ^ (n + 1) := by rw [Submodule.pow_succ, Submodule.pow_succ, ih]
    rw [hstep, h]

end Semiring

section Ring

variable {B : Type*} [Ring B]

/-- The submonoid `1 + I` of `B`, for an ideal `I`. It is multiplicatively closed because
`ab - 1 = a(b - 1) + (a - 1)`, which needs only closure of `I` under left multiplication. -/
def oneAdd (I : _root_.Ideal B) : Submonoid B where
  carrier := {x | x - 1 ∈ I}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have h : a * b - 1 = a * (b - 1) + (a - 1) := by
      rw [mul_sub, mul_one]; abel
    rw [h]
    exact I.add_mem (I.mul_mem_left _ hb) ha

@[simp]
theorem mem_oneAdd {I : _root_.Ideal B} {x : B} : x ∈ I.oneAdd ↔ x - 1 ∈ I := Iff.rfl

end Ring

section CommRing

variable {B : Type*} [CommRing B]

/-- If some `i ∈ I` is such that `1 + i` annihilates `I ^ n`, then `I ^ (n + 1) = I ^ n`. -/
theorem pow_succ_eq_pow_of_forall_mul_eq_zero {I : _root_.Ideal B} {i : B} (hi : i ∈ I) {n : ℕ}
    (h : ∀ x ∈ I ^ n, (1 + i) * x = 0) : I ^ (n + 1) = I ^ n := by
  refine le_antisymm (_root_.Ideal.pow_le_pow_right (Nat.le_succ n)) fun x hx ↦ ?_
  have hx0 : x = -(x * i) := by
    have hxx : (1 + i) * x = 0 := h x hx
    have hsum : x * i + x = 0 := by rw [← hxx]; ring
    exact eq_neg_of_add_eq_zero_right hsum
  rw [hx0, pow_succ]
  exact neg_mem (mul_mem_mul hx hi)

/-- Under the same hypothesis, the powers of `I` are constant from `n` on. -/
theorem pow_eq_pow_of_forall_mul_eq_zero {I : _root_.Ideal B} {i : B} (hi : i ∈ I) {n : ℕ}
    (h : ∀ x ∈ I ^ n, (1 + i) * x = 0) {k : ℕ} (hk : n ≤ k) : I ^ k = I ^ n :=
  pow_eq_pow_of_pow_succ_eq_pow (pow_succ_eq_pow_of_forall_mul_eq_zero hi h) hk

end CommRing

end Ideal
