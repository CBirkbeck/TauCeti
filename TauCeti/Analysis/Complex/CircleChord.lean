/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The polar chord identity on the unit circle

The difference of two unit-circle points in polar form: the half-angle sine, rotated a
quarter turn past the midpoint direction. This is the pointwise input for the endpoint
logarithms of circular contour arcs; its norm is `TauCeti.dist_circleExp_eq_two_mul_abs_sin`.

## Main declarations

* `TauCeti.exp_mul_I_sub_exp_mul_I`.
-/

public section

open Complex

namespace TauCeti

/-- **The polar chord identity on the unit circle**: the difference of two unit-circle
points is the half-angle sine, rotated a quarter turn past the midpoint direction. -/
theorem exp_mul_I_sub_exp_mul_I (α β : ℝ) :
    Complex.exp (α * Complex.I) - Complex.exp (β * Complex.I) =
      2 * (Real.sin ((α - β) / 2) : ℂ) * Complex.I *
        Complex.exp ((((α + β) / 2 : ℝ) : ℂ) * Complex.I) := by
  have hsin : Complex.exp ((((α - β) / 2 : ℝ) : ℂ) * Complex.I) -
      Complex.exp (-(((α - β) / 2 : ℝ) : ℂ) * Complex.I) =
      2 * Complex.sin (((α - β) / 2 : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin]
    field_simp
    rw [Complex.I_sq]
    ring
  have h1 : (α : ℂ) * Complex.I =
      ((α + β) / 2 : ℝ) * Complex.I + (((α - β) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : (β : ℂ) * Complex.I =
      ((α + β) / 2 : ℝ) * Complex.I + -(((α - β) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1, h2, Complex.exp_add, Complex.exp_add, ← mul_sub, hsin, ← Complex.ofReal_sin]
  ring

end TauCeti

end
