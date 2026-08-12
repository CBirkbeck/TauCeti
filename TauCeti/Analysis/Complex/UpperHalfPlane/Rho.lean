/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# The inversion at the elliptic corner `ρ`

Mathlib gives `ρ` its square (`UpperHalfPlane.ρ_sq`) and its norm (`UpperHalfPlane.norm_ρ`).
This file adds how `ρ` behaves under the inversion `z ↦ -1/z`, which is what the two `ρ`-corners
of the standard fundamental domain need: the inversion swaps them, carrying `ρ` to `ρ + 1` and
back.

Both identities fall straight out of `ρ_sq : (ρ : ℂ) ^ 2 = -ρ - 1`, once the relevant denominator
is known to be nonzero — and `ρ + 1 ≠ 0` is itself read off from `-1 / ρ = ρ + 1`.

## Main results

* `UpperHalfPlane.neg_one_div_ρ`: the inversion carries `ρ` to `ρ + 1`.
* `UpperHalfPlane.neg_one_div_ρ_add_one`: the inversion carries `ρ + 1` to `ρ`.
-/

public section

open Complex

namespace UpperHalfPlane

@[simp]
lemma ρ_ne_zero : (ρ : ℂ) ≠ 0 := fun h0 ↦ by simpa [h0] using norm_ρ

/-- The inversion carries `ρ` to `ρ + 1`. -/
@[simp]
lemma neg_one_div_ρ : -1 / (ρ : ℂ) = (ρ : ℂ) + 1 := by
  rw [div_eq_iff ρ_ne_zero]
  linear_combination -ρ_sq

/-- The second `ρ`-corner has unit modulus, like `ρ` itself: the inversion carries one to the
other and preserves the norm. -/
@[simp]
lemma norm_ρ_add_one : ‖(ρ : ℂ) + 1‖ = 1 := by
  rw [← neg_one_div_ρ, norm_div, norm_neg, norm_one, norm_ρ, div_one]

@[simp]
lemma ρ_add_one_ne_zero : (ρ : ℂ) + 1 ≠ 0 := by
  rw [← neg_one_div_ρ]
  exact div_ne_zero (by norm_num) ρ_ne_zero

/-- The inversion carries `ρ + 1` to `ρ`. -/
@[simp]
lemma neg_one_div_ρ_add_one : -1 / ((ρ : ℂ) + 1) = (ρ : ℂ) := by
  rw [div_eq_iff ρ_add_one_ne_zero]
  linear_combination -ρ_sq

end UpperHalfPlane
