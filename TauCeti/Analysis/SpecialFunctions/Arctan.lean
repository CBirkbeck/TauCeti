/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Complementary arctangents of a ratio and its reciprocal

Mathlib records the complementary-angle identity for `arctan` in reciprocal form,
`Real.arctan_inv_of_pos : 0 < x → arctan x⁻¹ = π / 2 - arctan x`.  A ratio of two positive reals
and the ratio the other way round are reciprocal, so their arctangents are complementary.

This is the form that arises whenever a rectangle in the plane is traversed: at a corner `(a, b)`
with `a, b > 0` the two sides subtend `arctan (a / b)` and `arctan (b / a)`, and the identity says
they make up the right angle.

## Main results

* `Real.arctan_div_add_arctan_div`: `arctan (a / b) + arctan (b / a) = π / 2` for `0 < a` and
  `0 < b`.
-/

public section

open Real

namespace Real

variable {a b : ℝ}

/-- **The arctangents of a ratio and of its reciprocal are complementary.**  For positive `a` and
`b` the angles `arctan (a / b)` and `arctan (b / a)` sum to a right angle. -/
theorem arctan_div_add_arctan_div (ha : 0 < a) (hb : 0 < b) :
    arctan (a / b) + arctan (b / a) = π / 2 := by
  rw [← inv_div a b, arctan_inv_of_pos (by positivity)]
  ring

end Real
