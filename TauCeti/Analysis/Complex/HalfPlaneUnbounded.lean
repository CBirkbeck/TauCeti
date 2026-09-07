/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Open half-planes of `ℂ` are unbounded

Each of the four open half-planes cut out by a bound on `re` or `im` contains points of
arbitrarily large norm. The witnesses are real or purely imaginary, so the norm is read off by
`Complex.norm_real`.

These are the hypotheses that winding-number vanishing arguments need: transporting a winding
number through an unbounded connected region requires exhibiting, for each radius, a point of
the region outside that radius.

## Main results

* `Complex.exists_im_lt_and_lt_norm`, `Complex.exists_lt_im_and_lt_norm`
* `Complex.exists_re_lt_and_lt_norm`, `Complex.exists_lt_re_and_lt_norm`
-/

public section

namespace Complex

/-- The open lower half-plane `{z | z.im < c}` is unbounded. -/
theorem exists_im_lt_and_lt_norm (c R : ℝ) : ∃ z : ℂ, z.im < c ∧ R < ‖z‖ := by
  refine ⟨((min c 0 - max R 0 - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · rw [Complex.mul_I_im, Complex.ofReal_re]
    nlinarith [min_le_left c 0, min_le_right c 0, le_max_right R 0]
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonpos (by nlinarith [min_le_right c 0, le_max_right R 0])]
    nlinarith [min_le_right c 0, le_max_left R 0]

/-- The open upper half-plane `{z | c < z.im}` is unbounded. -/
theorem exists_lt_im_and_lt_norm (c R : ℝ) : ∃ z : ℂ, c < z.im ∧ R < ‖z‖ := by
  refine ⟨((max c 0 + max R 0 + 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · rw [Complex.mul_I_im, Complex.ofReal_re]
    nlinarith [le_max_left c 0, le_max_right R 0]
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by nlinarith [le_max_right c 0, le_max_right R 0])]
    nlinarith [le_max_right c 0, le_max_left R 0]

/-- The open left half-plane `{z | z.re < c}` is unbounded. -/
theorem exists_re_lt_and_lt_norm (c R : ℝ) : ∃ z : ℂ, z.re < c ∧ R < ‖z‖ := by
  refine ⟨((min c 0 - max R 0 - 1 : ℝ) : ℂ), ?_, ?_⟩
  · rw [Complex.ofReal_re]
    nlinarith [min_le_left c 0, min_le_right c 0, le_max_right R 0]
  · rw [Complex.norm_real,
      Real.norm_of_nonpos (by nlinarith [min_le_right c 0, le_max_right R 0])]
    nlinarith [min_le_right c 0, le_max_left R 0]

/-- The open right half-plane `{z | c < z.re}` is unbounded. -/
theorem exists_lt_re_and_lt_norm (c R : ℝ) : ∃ z : ℂ, c < z.re ∧ R < ‖z‖ := by
  refine ⟨((max c 0 + max R 0 + 1 : ℝ) : ℂ), ?_, ?_⟩
  · rw [Complex.ofReal_re]
    nlinarith [le_max_left c 0, le_max_right R 0]
  · rw [Complex.norm_real,
      Real.norm_of_nonneg (by nlinarith [le_max_right c 0, le_max_right R 0])]
    nlinarith [le_max_right c 0, le_max_left R 0]

end Complex
