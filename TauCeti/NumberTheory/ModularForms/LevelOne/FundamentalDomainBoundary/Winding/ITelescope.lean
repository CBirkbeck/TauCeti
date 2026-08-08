/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.IGeometry

import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Complex.LogBranch
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The logarithmic telescope of the shifted contour at `i`

Over the `δ`-excluded parameter ranges `[0, 2-δ]` and `[2+δ, 5]`, the logarithmic
integral of the shifted contour `t ↦ fdBoundary H t - i` telescopes through the
boundary-tolerant logarithmic FTC piece by piece: the value is the difference of
endpoint logarithms minus `2πi`, the branch crossing contributed by the left vertical
through the height-`1` crossing.

## Main declarations

* `TauCeti.ModularForm.ftc_logDeriv_telescope_I` (the telescope; the analytic core of
  the generalized winding number `-1/2` at `i`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/I.lean`) this file ports onto
  the current Mathlib pin.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti

namespace ModularForm

variable {H δ : ℝ}

/-- The corner row lies strictly below `1`. -/
private lemma sqrt_three_div_two_lt_one : Real.sqrt 3 / 2 < 1 := by
  nlinarith [Real.sq_sqrt (by positivity : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]

/-- The right-vertical piece `[0, 1]` of the telescope: the shifted contour stays in the
right half-plane, so the logarithmic integral is a difference of principal logarithms. -/
private lemma telescope_piece_right_vertical (H : ℝ) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume 0 1 ∧
    ∫ t in (0 : ℝ)..1,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (fdBoundary H 1 - Complex.I) - Complex.log (fdBoundary H 0 - Complex.I) := by
  have heval : ∀ s ∈ Icc (0 : ℝ) 1, fdBoundary H s = fdBoundary_segment1 H s := fun s hs ↦
    fdBoundary_of_le_one hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment1 H s - Complex.I) =
      fun _ ↦ (UpperHalfPlane.ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment1]
  exact Contour.intervalIntegrable_and_integral_deriv_div_eq_log_of_slitPlane
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment1 H s - Complex.I) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment1 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment1 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_I_mem_slitPlane_of_lt_two H ⟨ht.1, by linarith [ht.2]⟩)
    (fun t ht ↦ congrArg (· - Complex.I) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - Complex.I) (heval 0 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - Complex.I) (heval 1 (right_mem_Icc.mpr (by norm_num))))

/-- The left arc piece `[1, 2-δ]` of the telescope: right of the top of the arc the
shifted contour stays in the slit plane. -/
private lemma telescope_piece_arc_left (H : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume 1 (2 - δ) ∧
    ∫ t in (1 : ℝ)..(2 - δ),
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (fdBoundary H (2 - δ) - Complex.I) -
        Complex.log (fdBoundary H 1 - Complex.I) := by
  have hab : (1 : ℝ) ≤ 2 - δ := by linarith
  have heval : ∀ s ∈ Icc (1 : ℝ) (2 - δ), fdBoundary H s = fdBoundary_segment2 s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · rw [← h1, fdBoundary_apply_one, fdBoundary_segment2_apply_one]
    · exact fdBoundary_of_le_two h1 (by linarith [hs.2])
  have hd : deriv (fun s ↦ fdBoundary_segment2 s - Complex.I) = fun s ↦
      (Real.pi / 2 - Real.pi / 3) •
        (circleMap 0 1 (Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment2]
  have hθc : Continuous fun s : ℝ ↦ Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3) := by
    fun_prop
  exact Contour.intervalIntegrable_and_integral_deriv_div_eq_log_of_slitPlane
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment2 s - Complex.I) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment2 s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment2 t).differentiableAt.sub_const _)
    (by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (Real.pi / 2 - Real.pi / 3)).continuousOn)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_I_mem_slitPlane_of_lt_two H ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t ht ↦ congrArg (· - Complex.I) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - Complex.I) (heval 1 (left_mem_Icc.mpr hab)))
    (congrArg (· - Complex.I) (heval (2 - δ) (right_mem_Icc.mpr hab)))

/-- The right arc piece `[2+δ, 3]` of the telescope: left of the top of the arc the
shifted contour stays in the slit plane. -/
private lemma telescope_piece_arc_right (H : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume (2 + δ) 3 ∧
    ∫ t in (2 + δ : ℝ)..3,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (fdBoundary H 3 - Complex.I) -
        Complex.log (fdBoundary H (2 + δ) - Complex.I) := by
  have hab : (2 + δ : ℝ) ≤ 3 := by linarith
  have heval : ∀ s ∈ Icc (2 + δ : ℝ) 3, fdBoundary H s = fdBoundary_segment3 s := fun s hs ↦
    fdBoundary_of_le_three (by linarith [hs.1]) hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment3 s - Complex.I) = fun s ↦
      (2 * Real.pi / 3 - Real.pi / 2) •
        (circleMap 0 1 (Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) *
          Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment3]
  have hθc : Continuous fun s : ℝ ↦
      Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2) := by
    fun_prop
  exact Contour.intervalIntegrable_and_integral_deriv_div_eq_log_of_slitPlane
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment3 s - Complex.I) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment3 s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment3 t).differentiableAt.sub_const _)
    (by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (2 * Real.pi / 3 - Real.pi / 2)).continuousOn)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_I_mem_slitPlane_of_two_lt H (by linarith [ht.1]) ht.2)
    (fun t ht ↦ congrArg (· - Complex.I) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - Complex.I) (heval (2 + δ) (left_mem_Icc.mpr hab)))
    (congrArg (· - Complex.I) (heval 3 (right_mem_Icc.mpr hab)))

/-- The lower left-vertical piece `[3, t₀]` of the telescope, up to the height-`1`
crossing: the shifted contour stays in the closed lower half-plane, so the logarithmic
integral evaluates against the negated arguments. -/
private lemma telescope_piece_left_lower (hH : 1 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume 3 (leftVerticalCrossingI H) ∧
    ∫ t in (3 : ℝ)..leftVerticalCrossingI H,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (-(fdBoundary H (leftVerticalCrossingI H) - Complex.I)) -
        Complex.log (-(fdBoundary H 3 - Complex.I)) := by
  have hHs : Real.sqrt 3 / 2 < H := by linarith [sqrt_three_div_two_lt_one]
  have hab : (3 : ℝ) ≤ leftVerticalCrossingI H := (three_lt_leftVerticalCrossingI hHs).le
  have hsub : Icc (3 : ℝ) (leftVerticalCrossingI H) ⊆ Icc (3 : ℝ) 4 :=
    Icc_subset_Icc le_rfl (leftVerticalCrossingI_lt_four hH).le
  have heval : ∀ s ∈ Icc (3 : ℝ) (leftVerticalCrossingI H),
      fdBoundary H s = fdBoundary_segment4 H s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h3 | h3
    · rw [← h3, fdBoundary_apply_three, fdBoundary_segment4_apply_three]
    · exact fdBoundary_of_le_four h3 (hsub hs).2
  have hd : deriv (fun s ↦ fdBoundary_segment4 H s - Complex.I) =
      fun _ ↦ -1 / 2 + H * Complex.I - (UpperHalfPlane.ρ : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment4]
  have hne : ∀ t ∈ Icc (3 : ℝ) (leftVerticalCrossingI H),
      fdBoundary H t - Complex.I ≠ 0 := by
    intro t ht h0
    have hre := re_fdBoundary_segment4 H (hsub ht)
    rw [sub_eq_zero] at h0
    rw [h0, Complex.I_re] at hre
    norm_num at hre
  refine Contour.intervalIntegrable_and_integral_deriv_div_eq_log_neg_of_im_nonpos
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment4 H s - Complex.I) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment4 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment4 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ ?_)
    (heval 3 (left_mem_Icc.mpr hab) ▸ hne 3 (left_mem_Icc.mpr hab))
    (heval _ (right_mem_Icc.mpr hab) ▸ hne _ (right_mem_Icc.mpr hab))
    (fun t ht ↦ ?_)
    (fun t ht ↦ congrArg (· - Complex.I) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - Complex.I) (heval 3 (left_mem_Icc.mpr hab)))
    (congrArg (· - Complex.I) (heval _ (right_mem_Icc.mpr hab)))
  · show (fdBoundary_segment4 H t - Complex.I).im ≤ 0
    rw [← heval t ht]
    rcases eq_or_lt_of_le ht.1 with h3 | h3
    · rw [← h3]
      exact (im_fdBoundary_sub_I_at_three_neg H).le
    · rcases eq_or_lt_of_le ht.2 with ht0 | ht0
      · rw [ht0]
        exact (im_fdBoundary_sub_I_leftVerticalCrossingI hH).le
      · exact (im_fdBoundary_sub_I_neg_of_lt_crossing hH h3 ht0).le
  · show -(fdBoundary_segment4 H t - Complex.I) ∈ Complex.slitPlane
    rw [← heval t ⟨ht.1.le, ht.2.le⟩]
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    have := im_fdBoundary_sub_I_neg_of_lt_crossing hH ht.1 ht.2
    simpa using ne_of_gt (by linarith : 0 < -(fdBoundary H t - Complex.I).im)

/-- The upper left-vertical piece `[t₀, 4]` of the telescope, above the height-`1`
crossing: the shifted contour stays in the closed upper half-plane. -/
private lemma telescope_piece_left_upper (hH : 1 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume (leftVerticalCrossingI H) 4 ∧
    ∫ t in (leftVerticalCrossingI H : ℝ)..4,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (fdBoundary H 4 - Complex.I) -
        Complex.log (fdBoundary H (leftVerticalCrossingI H) - Complex.I) := by
  have hHs : Real.sqrt 3 / 2 < H := by linarith [sqrt_three_div_two_lt_one]
  have hab : leftVerticalCrossingI H ≤ (4 : ℝ) := (leftVerticalCrossingI_lt_four hH).le
  have hsub : Icc (leftVerticalCrossingI H) (4 : ℝ) ⊆ Icc (3 : ℝ) 4 :=
    Icc_subset_Icc (three_lt_leftVerticalCrossingI hHs).le le_rfl
  have heval : ∀ s ∈ Icc (leftVerticalCrossingI H) (4 : ℝ),
      fdBoundary H s = fdBoundary_segment4 H s := fun s hs ↦
    fdBoundary_of_le_four (lt_of_lt_of_le (three_lt_leftVerticalCrossingI hHs) hs.1) hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment4 H s - Complex.I) =
      fun _ ↦ -1 / 2 + H * Complex.I - (UpperHalfPlane.ρ : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment4]
  have hne : ∀ t ∈ Icc (leftVerticalCrossingI H) (4 : ℝ),
      fdBoundary H t - Complex.I ≠ 0 := by
    intro t ht h0
    have hre := re_fdBoundary_segment4 H (hsub ht)
    rw [sub_eq_zero] at h0
    rw [h0, Complex.I_re] at hre
    norm_num at hre
  have him : ∀ t ∈ Icc (leftVerticalCrossingI H) (4 : ℝ),
      0 ≤ (fdBoundary H t - Complex.I).im := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [← ht0]
      exact (im_fdBoundary_sub_I_leftVerticalCrossingI hH).ge
    · exact (im_fdBoundary_sub_I_pos_of_crossing_lt hH ht0 ht.2).le
  refine Contour.intervalIntegrable_and_integral_deriv_div_eq_log_of_im_nonneg
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment4 H s - Complex.I) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment4 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment4 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ him t ht)
    (heval _ (left_mem_Icc.mpr hab) ▸ hne _ (left_mem_Icc.mpr hab))
    (heval 4 (right_mem_Icc.mpr hab) ▸ hne 4 (right_mem_Icc.mpr hab))
    (fun t ht ↦ ?_)
    (fun t ht ↦ congrArg (· - Complex.I) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - Complex.I) (heval _ (left_mem_Icc.mpr hab)))
    (congrArg (· - Complex.I) (heval 4 (right_mem_Icc.mpr hab)))
  have hpos := im_fdBoundary_sub_I_pos_of_crossing_lt hH ht.1 ht.2.le
  rw [heval t ⟨ht.1.le, ht.2.le⟩] at hpos
  exact Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hpos))

/-- The ceiling piece `[4, 5]` of the telescope: the shifted contour stays at height
`H - 1 > 0`, inside the slit plane. -/
private lemma telescope_piece_ceiling (hH : 1 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume 4 5 ∧
    ∫ t in (4 : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (fdBoundary H 5 - Complex.I) - Complex.log (fdBoundary H 4 - Complex.I) := by
  have heval : ∀ s ∈ Icc (4 : ℝ) 5, fdBoundary H s = fdBoundary_segment5 H s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h4 | h4
    · rw [← h4, fdBoundary_apply_four, fdBoundary_segment5_apply_four]
    · exact fdBoundary_of_gt_four h4
  have hd : deriv (fun s ↦ fdBoundary_segment5 H s - Complex.I) = fun _ ↦ (1 : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment5]
  have hslit : ∀ t ∈ Icc (4 : ℝ) 5, fdBoundary H t - Complex.I ∈ Complex.slitPlane := by
    intro t ht
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    rw [Complex.sub_im, Complex.I_im, im_fdBoundary_segment5 H ht]
    linarith
  exact Contour.intervalIntegrable_and_integral_deriv_div_eq_log_of_slitPlane
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment5 H s - Complex.I) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment5 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment5 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ hslit t ht)
    (fun t ht ↦ congrArg (· - Complex.I) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - Complex.I) (heval 4 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - Complex.I) (heval 5 (right_mem_Icc.mpr (by norm_num))))

/-- For a point on the open negative real axis, the logarithm of the negation loses
`π·i`. -/
private lemma log_neg_eq_log_sub_pi_mul_I {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    Complex.log (-z) = Complex.log z - Real.pi * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re]
  · rw [Complex.log_im, Complex.sub_im, Complex.log_im,
      Complex.arg_eq_pi_iff.mpr ⟨hre, him⟩,
      Complex.arg_eq_zero_iff.mpr ⟨by simpa using hre.le, by simpa using him⟩]
    simp

/-- **The logarithmic telescope at `i`**: over the `δ`-excluded ranges the logarithmic
integral of the shifted contour is integrable and evaluates to the endpoint logarithms
minus the branch crossing `2πi`. -/
theorem ftc_logDeriv_telescope_I (H : ℝ) (hH : 1 < H) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume 0 (2 - δ) ∧
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume (2 + δ) 5 ∧
    (∫ t in (0 : ℝ)..(2 - δ),
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I)) +
      (∫ t in (2 + δ : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I)) =
      Complex.log (fdBoundary H (2 - δ) - Complex.I) -
        Complex.log (fdBoundary H (2 + δ) - Complex.I) - 2 * Real.pi * Complex.I := by
  obtain ⟨hi01, he01⟩ := telescope_piece_right_vertical H
  obtain ⟨hi12, he12⟩ := telescope_piece_arc_left H hδ hδ1
  obtain ⟨hi23, he23⟩ := telescope_piece_arc_right H hδ hδ1
  obtain ⟨hi3c, he3c⟩ := telescope_piece_left_lower hH
  obtain ⟨hic4, hec4⟩ := telescope_piece_left_upper hH
  obtain ⟨hi45, he45⟩ := telescope_piece_ceiling hH
  have hint34 := hi3c.trans hic4
  have hint35 := hint34.trans hi45
  refine ⟨hi01.trans hi12, hi23.trans hint35, ?_⟩
  have hlog3 : Complex.log (-(fdBoundary H 3 - Complex.I)) =
      Complex.log (fdBoundary H 3 - Complex.I) + Real.pi * Complex.I :=
    log_neg_eq_log_add_pi_mul_I_of_im_neg (im_fdBoundary_sub_I_at_three_neg H)
  have hlogt0 : Complex.log (-(fdBoundary H (leftVerticalCrossingI H) - Complex.I)) =
      Complex.log (fdBoundary H (leftVerticalCrossingI H) - Complex.I) -
        Real.pi * Complex.I := by
    refine log_neg_eq_log_sub_pi_mul_I ?_ (im_fdBoundary_sub_I_leftVerticalCrossingI hH)
    rw [Complex.sub_re, Complex.I_re, re_fdBoundary_segment4 H
      ⟨(three_lt_leftVerticalCrossingI (by linarith [sqrt_three_div_two_lt_one])).le,
        (leftVerticalCrossingI_lt_four hH).le⟩]
    norm_num
  have hlog50 : Complex.log (fdBoundary H 5 - Complex.I) =
      Complex.log (fdBoundary H 0 - Complex.I) := by
    rw [fdBoundary_apply_five, fdBoundary_apply_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi01 hi12,
    ← intervalIntegral.integral_add_adjacent_intervals hi23 hint35,
    ← intervalIntegral.integral_add_adjacent_intervals hint34 hi45,
    ← intervalIntegral.integral_add_adjacent_intervals hi3c hic4,
    he01, he12, he23, he3c, hec4, he45, hlog3, hlogt0, hlog50]
  ring

end ModularForm

end TauCeti

end
