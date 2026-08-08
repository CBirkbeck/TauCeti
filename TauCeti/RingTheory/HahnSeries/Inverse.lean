/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.HahnSeries.Summable

/-!
# `orderTop` and `leadingCoeff` of inverses and quotients of Hahn series

Over a field of coefficients, a nonzero Hahn series is invertible, and both of the invariants
Mathlib attaches to a Hahn series — its `orderTop` and its `leadingCoeff` — are multiplicative
(`HahnSeries.orderTop_mul`, `HahnSeries.leadingCoeff_mul`). This file records what that gives for
inversion and division, which Mathlib states for products only.

## Main results

* `HahnSeries.orderTop_inv_eq_neg`: `s⁻¹.orderTop = -s.orderTop` for `s ≠ 0`.
* `HahnSeries.orderTop_div`: `(s / t).orderTop = s.orderTop - t.orderTop` for `t ≠ 0`.
* `HahnSeries.leadingCoeff_inv`: `s⁻¹.leadingCoeff = s.leadingCoeff⁻¹` for `s ≠ 0`.
* `HahnSeries.leadingCoeff_div`: `(s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/HahnSeriesAux.lean`, declarations `orderTop_inv_eq_neg`, `orderTop_div`,
`leadingCoeff_inv` and `leadingCoeff_div`. The source file marks all four as upstream candidates.
-/

public section

namespace HahnSeries

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable {R : Type*} [Field R] {s t : HahnSeries Γ R}

/-- The `orderTop` of the inverse of a nonzero Hahn series over a field is the negation of its
`orderTop`. -/
theorem orderTop_inv_eq_neg (hs : s ≠ 0) : s⁻¹.orderTop = -s.orderTop := by
  -- `s * s⁻¹ = 1` has `orderTop` zero, and `orderTop` is additive on products.
  have hmul : (s * s⁻¹).orderTop = s.orderTop + s⁻¹.orderTop := orderTop_mul s s⁻¹
  rw [mul_inv_cancel₀ hs, orderTop_one] at hmul
  -- Both orders are finite, so the equation may be read in `Γ`.
  lift s.orderTop to Γ using orderTop_ne_top.mpr hs with a
  lift s⁻¹.orderTop to Γ using orderTop_ne_top.mpr (inv_ne_zero hs) with b
  rw [← WithTop.coe_add, show (0 : WithTop Γ) = ((0 : Γ) : WithTop Γ) from rfl,
    WithTop.coe_eq_coe] at hmul
  rw [show b = -a from eq_neg_of_add_eq_zero_right hmul.symm]
  rfl

/-- The `orderTop` of a quotient of Hahn series over a field is the difference of the `orderTop`s
of numerator and denominator. -/
theorem orderTop_div (ht : t ≠ 0) : (s / t).orderTop = s.orderTop - t.orderTop := by
  rw [div_eq_mul_inv, orderTop_mul s t⁻¹, orderTop_inv_eq_neg ht, sub_eq_add_neg]

/-- The leading coefficient of the inverse of a nonzero Hahn series over a field is the inverse of
its leading coefficient. -/
theorem leadingCoeff_inv (hs : s ≠ 0) : s⁻¹.leadingCoeff = s.leadingCoeff⁻¹ := by
  have hmul : (s * s⁻¹).leadingCoeff = s.leadingCoeff * s⁻¹.leadingCoeff := leadingCoeff_mul s s⁻¹
  rw [mul_inv_cancel₀ hs, leadingCoeff_one] at hmul
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm, ← hmul])

/-- The leading coefficient of a quotient of Hahn series over a field is the quotient of the
leading coefficients. -/
theorem leadingCoeff_div (ht : t ≠ 0) :
    (s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff := by
  rw [div_eq_mul_inv, leadingCoeff_mul, leadingCoeff_inv ht, div_eq_mul_inv]

end HahnSeries
