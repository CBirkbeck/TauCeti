/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The winding number of each boundary piece is a principal logarithm

Each smooth piece of the boundary contour of the truncated fundamental domain is confined
to an axis-aligned half-plane: the verticals have constant real part `±1/2`, the arc stays
below height `1`, and the truncation ceiling has constant height `H`. About a point `w` on
the far side of the corresponding line, the chord ratios of the piece therefore lie in the
slit plane, so its index integral is a principal logarithm of the endpoint ratio and the
winding number of the piece is `(2πi)⁻¹` times that logarithm.

Summing the four values over the piece decomposition and pinning with integrality is how
the interior winding number `-1` of the contour is computed.

## Main declarations

* `TauCeti.ModularForm.re_fdBoundary_segment1`, `…_segment4`, `…_segment5`,
  `TauCeti.ModularForm.im_fdBoundary_arc_le` — the half-plane confinements.
* `TauCeti.ModularForm.windingNumber_fdBoundary_segment1_eq_log`, `…_arc_eq_log`,
  `…_segment4_eq_log`, `…_segment5_eq_log` — the four logarithm values.

## References

The piece-logarithm evaluation follows the fundamental-domain boundary development of
AINTLIB's `LeanModularForms` (`ForMathlib/FDBoundary.lean`, `FDBoundaryH.lean`,
`FDBoundaryPath.lean`); the logarithm FTC and the slit-plane criteria are Tau Ceti's.
-/

public section

open Set TauCeti.Contour UpperHalfPlane

namespace TauCeti

namespace ModularForm

variable {H t : ℝ} {w : ℂ}

/-- The right vertical has constant real part `1/2`. -/
theorem re_fdBoundary_segment1 (H : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (fdBoundary H t).re = 1 / 2 := by
  rw [eqOn_fdBoundary_segment1 H ht, fdBoundary_segment1_apply, AffineMap.lineMap_apply]
  simp [ρ, Complex.real_smul]
  norm_num

/-- The arc stays at height at most `1`. -/
theorem im_fdBoundary_arc_le (H : ℝ) (ht : t ∈ Icc (1 : ℝ) 3) :
    (fdBoundary H t).im ≤ 1 := by
  rw [eqOn_fdBoundary_arc H ht, circleMap_zero_im]
  simpa using Real.sin_le_one ((t + 1) * (Real.pi / 6))

/-- The left vertical has constant real part `-1/2`. -/
theorem re_fdBoundary_segment4 (H : ℝ) (ht : t ∈ Icc (3 : ℝ) 4) :
    (fdBoundary H t).re = -(1 / 2) := by
  rw [eqOn_fdBoundary_segment4 H ht, fdBoundary_segment4_apply, AffineMap.lineMap_apply]
  simp [ρ, Complex.real_smul]
  norm_num

/-- The truncation ceiling has constant height `H`. -/
theorem im_fdBoundary_segment5 (H : ℝ) (ht : t ∈ Icc (4 : ℝ) 5) :
    (fdBoundary H t).im = H := by
  rw [eqOn_fdBoundary_segment5 H ht, fdBoundary_segment5_apply, AffineMap.lineMap_apply]
  simp [Complex.real_smul]

/-- The winding number of the right vertical about a point strictly to its left is the
principal logarithm of the endpoint ratio. -/
theorem windingNumber_fdBoundary_segment1_eq_log (hw : w.re < 1 / 2) :
    windingNumber (fdBoundary H) 0 1 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.log (((ρ : ℂ) + 1 - w) / (1 / 2 + H * Complex.I - w)) := by
  have h01 : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le (by norm_num)
  have hre : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < (fdBoundary H t - w).re := fun t ht => by
    rw [Complex.sub_re, re_fdBoundary_segment1 H (h01 ▸ ht)]
    linarith
  have h_avoid : ∀ t ∈ uIcc (0 : ℝ) 1, fdBoundary H t ≠ w := fun t ht h_eq =>
    absurd (hre t ht) (by simp [h_eq])
  have h_int := intervalIntegrable_inv_sub_mul_deriv (continuous_fdBoundary H).continuousOn
    h_avoid ((isPiecewiseC1On_fdBoundary H).intervalIntegrable_deriv.mono_set
      (by rw [h01, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
          exact Icc_subset_Icc le_rfl (by norm_num)))
  have h_diff : ∀ s ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1) \ (∅ : Set ℝ),
      DifferentiableAt ℝ (fdBoundary H) s := by
    intro s hs
    rw [sdiff_empty, min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] at hs
    exact (hasDerivAt_fdBoundary_of_lt_one hs.2).differentiableAt
  have h_slit : ∀ t ∈ uIcc (0 : ℝ) 1,
      (fdBoundary H t - w) / (fdBoundary H 0 - w) ∈ Complex.slitPlane := fun t ht =>
    div_mem_slitPlane_of_re_pos (hre 0 left_mem_uIcc) (hre t ht)
  rw [windingNumber_eq_integral_of_avoidance (continuous_fdBoundary H).continuousOn
      h_avoid h_int,
    integral_inv_sub_mul_deriv_eq_log countable_empty (continuous_fdBoundary H).continuousOn
      h_diff h_slit h_int,
    fdBoundary_apply_one, fdBoundary_apply_zero]

/-- The winding number of the arc about a point strictly above height `1` is the principal
logarithm of the endpoint ratio. -/
theorem windingNumber_fdBoundary_arc_eq_log (hw : 1 < w.im) :
    windingNumber (fdBoundary H) 1 3 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.log (((ρ : ℂ) - w) / ((ρ : ℂ) + 1 - w)) := by
  have h13 : uIcc (1 : ℝ) 3 = Icc 1 3 := uIcc_of_le (by norm_num)
  have him : ∀ t ∈ uIcc (1 : ℝ) 3, (fdBoundary H t - w).im < 0 := fun t ht => by
    have := im_fdBoundary_arc_le H (h13 ▸ ht)
    rw [Complex.sub_im]
    linarith
  have h_avoid : ∀ t ∈ uIcc (1 : ℝ) 3, fdBoundary H t ≠ w := fun t ht h_eq =>
    absurd (him t ht) (by simp [h_eq])
  have h_int := intervalIntegrable_inv_sub_mul_deriv (continuous_fdBoundary H).continuousOn
    h_avoid ((isPiecewiseC1On_fdBoundary H).intervalIntegrable_deriv.mono_set
      (by rw [h13, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
          exact Icc_subset_Icc (by norm_num) (by norm_num)))
  have h_diff : ∀ s ∈ Ioo (min (1 : ℝ) 3) (max (1 : ℝ) 3) \ (∅ : Set ℝ),
      DifferentiableAt ℝ (fdBoundary H) s := by
    intro s hs
    rw [sdiff_empty, min_eq_left (by norm_num : (1 : ℝ) ≤ 3),
      max_eq_right (by norm_num : (1 : ℝ) ≤ 3)] at hs
    exact (hasDerivAt_fdBoundary_of_mem_Ioo_one_three hs).differentiableAt
  have h_slit : ∀ t ∈ uIcc (1 : ℝ) 3,
      (fdBoundary H t - w) / (fdBoundary H 1 - w) ∈ Complex.slitPlane := fun t ht =>
    div_mem_slitPlane_of_im_neg (him 1 left_mem_uIcc) (him t ht)
  rw [windingNumber_eq_integral_of_avoidance (continuous_fdBoundary H).continuousOn
      h_avoid h_int,
    integral_inv_sub_mul_deriv_eq_log countable_empty (continuous_fdBoundary H).continuousOn
      h_diff h_slit h_int,
    fdBoundary_apply_three, fdBoundary_apply_one]

/-- The winding number of the left vertical about a point strictly to its right is the
principal logarithm of the endpoint ratio. -/
theorem windingNumber_fdBoundary_segment4_eq_log (hw : -(1 / 2) < w.re) :
    windingNumber (fdBoundary H) 3 4 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.log ((-1 / 2 + H * Complex.I - w) / ((ρ : ℂ) - w)) := by
  have h34 : uIcc (3 : ℝ) 4 = Icc 3 4 := uIcc_of_le (by norm_num)
  have hre : ∀ t ∈ uIcc (3 : ℝ) 4, (fdBoundary H t - w).re < 0 := fun t ht => by
    rw [Complex.sub_re, re_fdBoundary_segment4 H (h34 ▸ ht)]
    linarith
  have h_avoid : ∀ t ∈ uIcc (3 : ℝ) 4, fdBoundary H t ≠ w := fun t ht h_eq =>
    absurd (hre t ht) (by simp [h_eq])
  have h_int := intervalIntegrable_inv_sub_mul_deriv (continuous_fdBoundary H).continuousOn
    h_avoid ((isPiecewiseC1On_fdBoundary H).intervalIntegrable_deriv.mono_set
      (by rw [h34, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
          exact Icc_subset_Icc (by norm_num) (by norm_num)))
  have h_diff : ∀ s ∈ Ioo (min (3 : ℝ) 4) (max (3 : ℝ) 4) \ (∅ : Set ℝ),
      DifferentiableAt ℝ (fdBoundary H) s := by
    intro s hs
    rw [sdiff_empty, min_eq_left (by norm_num : (3 : ℝ) ≤ 4),
      max_eq_right (by norm_num : (3 : ℝ) ≤ 4)] at hs
    exact (hasDerivAt_fdBoundary_of_mem_Ioo_three_four hs).differentiableAt
  have h_slit : ∀ t ∈ uIcc (3 : ℝ) 4,
      (fdBoundary H t - w) / (fdBoundary H 3 - w) ∈ Complex.slitPlane := fun t ht =>
    div_mem_slitPlane_of_re_neg (hre 3 left_mem_uIcc) (hre t ht)
  rw [windingNumber_eq_integral_of_avoidance (continuous_fdBoundary H).continuousOn
      h_avoid h_int,
    integral_inv_sub_mul_deriv_eq_log countable_empty (continuous_fdBoundary H).continuousOn
      h_diff h_slit h_int,
    fdBoundary_apply_four, fdBoundary_apply_three]

/-- The winding number of the truncation ceiling about a point strictly below height `H` is
the principal logarithm of the endpoint ratio. -/
theorem windingNumber_fdBoundary_segment5_eq_log (hw : w.im < H) :
    windingNumber (fdBoundary H) 4 5 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.log ((1 / 2 + H * Complex.I - w) / (-1 / 2 + H * Complex.I - w)) := by
  have h45 : uIcc (4 : ℝ) 5 = Icc 4 5 := uIcc_of_le (by norm_num)
  have him : ∀ t ∈ uIcc (4 : ℝ) 5, 0 < (fdBoundary H t - w).im := fun t ht => by
    rw [Complex.sub_im, im_fdBoundary_segment5 H (h45 ▸ ht)]
    linarith
  have h_avoid : ∀ t ∈ uIcc (4 : ℝ) 5, fdBoundary H t ≠ w := fun t ht h_eq =>
    absurd (him t ht) (by simp [h_eq])
  have h_int := intervalIntegrable_inv_sub_mul_deriv (continuous_fdBoundary H).continuousOn
    h_avoid ((isPiecewiseC1On_fdBoundary H).intervalIntegrable_deriv.mono_set
      (by rw [h45, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
          exact Icc_subset_Icc (by norm_num) le_rfl))
  have h_diff : ∀ s ∈ Ioo (min (4 : ℝ) 5) (max (4 : ℝ) 5) \ (∅ : Set ℝ),
      DifferentiableAt ℝ (fdBoundary H) s := by
    intro s hs
    rw [sdiff_empty, min_eq_left (by norm_num : (4 : ℝ) ≤ 5),
      max_eq_right (by norm_num : (4 : ℝ) ≤ 5)] at hs
    exact (hasDerivAt_fdBoundary_of_gt_four hs.1).differentiableAt
  have h_slit : ∀ t ∈ uIcc (4 : ℝ) 5,
      (fdBoundary H t - w) / (fdBoundary H 4 - w) ∈ Complex.slitPlane := fun t ht =>
    div_mem_slitPlane_of_im_pos (him 4 left_mem_uIcc) (him t ht)
  rw [windingNumber_eq_integral_of_avoidance (continuous_fdBoundary H).continuousOn
      h_avoid h_int,
    integral_inv_sub_mul_deriv_eq_log countable_empty (continuous_fdBoundary H).continuousOn
      h_diff h_slit h_int,
    fdBoundary_apply_five, fdBoundary_apply_four]

end ModularForm

end TauCeti

end
