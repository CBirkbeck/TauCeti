/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.Basic

/-!
# Stabilization of the powers of a finitely generated ideal

The commutative-algebra half of Wedhorn's Proposition 7.49(2). If a finitely generated ideal `I`
of a commutative ring `B` becomes zero after localizing at the submonoid `1 + I`, then the powers
of `I` stabilize: `I ^ k = I ^ n` for all `k ≥ n`.

## Main definitions

* `Ideal.oneAdd`: the submonoid `1 + I` of `B`.

## Main results

* `Ideal.pow_eq_pow_of_forall_mul_eq_zero`: the stabilization step, from an element `i ∈ I` that
  annihilates `I ^ n` through `1 + i`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], proof of Proposition 7.49(2).
-/

public section

variable {B : Type*} [CommRing B]

namespace Ideal

/-- The submonoid `1 + I` of `B`, for an ideal `I`. It is multiplicatively closed because
`(1 + a)(1 + b) = 1 + (a + ab + b)`. This is the submonoid Wedhorn localizes at in the proof of
Proposition 7.49(2). -/
def oneAdd (I : _root_.Ideal B) : Submonoid B where
  carrier := {x | x - 1 ∈ I}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have h : a * b - 1 = (a - 1) * b + (b - 1) := by ring
    rw [h]
    exact I.add_mem (I.mul_mem_right _ ha) hb

@[simp]
theorem mem_oneAdd {I : _root_.Ideal B} {x : B} : x ∈ I.oneAdd ↔ x - 1 ∈ I := Iff.rfl

/-- **The stabilization step in Wedhorn's Proposition 7.49(2).** If some `i ∈ I` is such that
`1 + i` annihilates `I ^ n`, then `I ^ (n + 1) = I ^ n`: for `x ∈ I ^ n` the relation
`(1 + i) * x = 0` reads `x = -(x * i)`, whose right-hand side lies in `I ^ n * I`. -/
theorem pow_succ_eq_pow_of_forall_mul_eq_zero {I : _root_.Ideal B} {i : B} (hi : i ∈ I) {n : ℕ}
    (h : ∀ x ∈ I ^ n, (1 + i) * x = 0) : I ^ (n + 1) = I ^ n := by
  refine le_antisymm (_root_.Ideal.pow_le_pow_right (Nat.le_succ n)) fun x hx ↦ ?_
  have hx0 : x = -(x * i) := by
    have hxx : (1 + i) * x = 0 := h x hx
    have hsum : x * i + x = 0 := by rw [← hxx]; ring
    exact eq_neg_of_add_eq_zero_right hsum
  rw [hx0, pow_succ]
  exact neg_mem (mul_mem_mul hx hi)

/-- The powers of `I` are constant from `n` on, under the same hypothesis. -/
theorem pow_eq_pow_of_forall_mul_eq_zero {I : _root_.Ideal B} {i : B} (hi : i ∈ I) {n : ℕ}
    (h : ∀ x ∈ I ^ n, (1 + i) * x = 0) {k : ℕ} (hk : n ≤ k) : I ^ k = I ^ n := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [← ih] at h ⊢
    exact pow_succ_eq_pow_of_forall_mul_eq_zero hi h

end Ideal
