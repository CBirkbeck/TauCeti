/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.PwC1ImmersionOn

/-!
# The direction in which a curve enters and leaves a crossing

At a parameter `t₀` where a curve meets a point `z₀`, the chord `γ t - z₀` shrinks to zero, but
its *direction* has one-sided limits: the curve leaves along the outgoing tangent `L₊` and
arrives along the reversed incoming tangent `-L₋`.

The reversal on the incoming side is the whole point. Approaching from the left, `t - t₀ < 0`, so
the chord `γ t - z₀ ≈ (t - t₀) · L₋` points *opposite* to the tangent. That is why the interior
angle of the sector swept at the crossing is measured from `-L₋` to `L₊`, as in
`TauCeti.Contour.crossingAngle`, rather than from `L₋` to `L₊`.

Both statements are exact rather than asymptotic: for `t ≠ t₀` the normalised chord *equals*
`±slope γ t₀ t / ‖slope γ t₀ t‖`, so the limits follow from the one-sided slope limits.

## Main results

* `TauCeti.Contour.tendsto_dir_sub_nhdsGT` — the outgoing direction limit.
* `TauCeti.Contour.tendsto_dir_sub_nhdsLT` — the incoming direction limit, reversed.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Proposition 2.2.
-/

public section

namespace TauCeti.Contour

open Filter Set Topology

variable {γ : ℝ → ℂ} {z₀ L : ℂ} {t₀ : ℝ}

/-- For `t > t₀`, the normalised chord from a crossing is the normalised slope: the positive
scalar `t - t₀` cancels. -/
private theorem dir_sub_eq_of_gt (hcross : γ t₀ = z₀) {t : ℝ} (ht : t₀ < t) :
    (γ t - z₀) / (‖γ t - z₀‖ : ℂ) =
      slope γ t₀ t / (‖slope γ t₀ t‖ : ℂ) := by
  have hpos : (0 : ℝ) < t - t₀ := sub_pos.mpr ht
  have hs : γ t - z₀ = ((t - t₀ : ℝ) : ℂ) * slope γ t₀ t := by
    rw [← hcross, ← Complex.real_smul]
    exact (sub_smul_slope γ t₀ t).symm
  rw [hs, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  push_cast
  exact mul_div_mul_left _ _
    (by exact_mod_cast Complex.ofReal_ne_zero.mpr hpos.ne' : ((t : ℂ) - (t₀ : ℂ)) ≠ 0)

/-- **The outgoing direction at a crossing.** As `t → t₀⁺`, the direction of the chord
`γ t - z₀` tends to that of the outgoing tangent. -/
theorem tendsto_dir_sub_nhdsGT (hcross : γ t₀ = z₀) (hL : L ≠ 0)
    (hslope : Tendsto (slope γ t₀) (𝓝[>] t₀) (𝓝 L)) :
    Tendsto (fun t => (γ t - z₀) / (‖γ t - z₀‖ : ℂ)) (𝓝[>] t₀) (𝓝 (L / (‖L‖ : ℂ))) := by
  have hnorm : Tendsto (fun t => ((‖slope γ t₀ t‖ : ℝ) : ℂ)) (𝓝[>] t₀) (𝓝 ((‖L‖ : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (hslope.norm)
  refine ((hslope.div hnorm (by simpa using hL)).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (dir_sub_eq_of_gt hcross ht).symm

/-- **The incoming direction at a crossing, reversed.** As `t → t₀⁻`, the direction of the chord
`γ t - z₀` tends to that of the *negated* incoming tangent, because `t - t₀` is negative. -/
theorem tendsto_dir_sub_nhdsLT (hcross : γ t₀ = z₀) (hL : L ≠ 0)
    (hslope : Tendsto (slope γ t₀) (𝓝[<] t₀) (𝓝 L)) :
    Tendsto (fun t => (γ t - z₀) / (‖γ t - z₀‖ : ℂ)) (𝓝[<] t₀) (𝓝 (-(L / (‖L‖ : ℂ)))) := by
  have hnorm : Tendsto (fun t => ((‖slope γ t₀ t‖ : ℝ) : ℂ)) (𝓝[<] t₀) (𝓝 ((‖L‖ : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (hslope.norm)
  have key : Tendsto (fun t => -(slope γ t₀ t / ((‖slope γ t₀ t‖ : ℝ) : ℂ))) (𝓝[<] t₀)
      (𝓝 (-(L / ((‖L‖ : ℝ) : ℂ)))) := (hslope.div hnorm (by simpa using hL)).neg
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hneg : (0 : ℝ) < t₀ - t := sub_pos.mpr ht
  have hne : ((t : ℂ) - (t₀ : ℂ)) ≠ 0 := by
    exact_mod_cast Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (by linarith : t ≠ t₀))
  have hs : γ t - z₀ = ((t - t₀ : ℝ) : ℂ) * slope γ t₀ t := by
    rw [← hcross, ← Complex.real_smul]
    exact (sub_smul_slope γ t₀ t).symm
  rw [hs, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  push_cast
  rw [neg_mul, div_neg, mul_div_mul_left _ _ hne]

end TauCeti.Contour
