/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.HahnSeries.Summable

/-!
# `leadingCoeff` of inverses and quotients of Hahn series

Over a field of coefficients a nonzero Hahn series is invertible, and `HahnSeries.leadingCoeff` is
multiplicative (`HahnSeries.leadingCoeff_mul`). This file records what that gives for inversion and
division, which Mathlib states for products only.

There is deliberately no `orderTop` counterpart here. The other invariant already has one, and a
better one: `HahnSeries.addVal` is an `AddValuation` whose value is `orderTop`
(`HahnSeries.addVal_apply`), so `AddValuation.map_inv` and `AddValuation.map_div` give
`s⁻¹.orderTop = -s.orderTop` and `(s / t).orderTop = s.orderTop - t.orderTop` directly — and
without any nonzero hypothesis, since `-⊤ = ⊤` in the value group.

## Main results

* `HahnSeries.leadingCoeff_inv`: `s⁻¹.leadingCoeff = s.leadingCoeff⁻¹` for `s ≠ 0`.
* `HahnSeries.leadingCoeff_div`: `(s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/HahnSeriesAux.lean`, declarations `leadingCoeff_inv` and `leadingCoeff_div`. That file's
two further declarations, `orderTop_inv_eq_neg` and `orderTop_div`, are **not** ported: they are
the `addVal` consequences described above, which the source predates.
-/

public section

namespace HahnSeries

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable {R : Type*} [Field R] {s t : HahnSeries Γ R}

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
