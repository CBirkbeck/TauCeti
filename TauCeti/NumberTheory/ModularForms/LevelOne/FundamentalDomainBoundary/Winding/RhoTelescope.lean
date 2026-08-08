/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Rho.Geometry

import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The logarithmic telescope of the shifted contour at `ρ`

Over the corner-excluded parameter ranges `[0, 3-δ_L]` and `[3+δ_R, 5]`, the logarithmic
integral of the shifted contour `t ↦ fdBoundary H t - ρ` telescopes through the
slit-plane logarithmic FTC piece by piece: every piece is slit-plane confined — the
contour never crosses the branch cut from `ρ` — so the value is exactly the difference
of the two endpoint logarithms beside the corner.

## Main declarations

* `TauCeti.ModularForm.ftc_logDeriv_telescope_rho` (the telescope; the analytic core of
  the generalized winding number `-1/6` at `ρ`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/Rho.lean`) this file ports onto
  the current Mathlib pin.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti

namespace ModularForm

variable {H δL δR : ℝ}

/-- The ordered slit-plane comparison step of the telescope: the canonical logarithmic FTC
`TauCeti.Contour.integral_deriv_div_eq_log_sub_log` applied to the comparison function, its
integrability from the continuous derivative, both transported to the contour across the
interior agreement. -/
private lemma slit_comparison {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b))
    (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_slit : ∀ t ∈ Icc a b, h t ∈ Complex.slitPlane)
    (heq : Set.EqOn g h (Ioo a b)) (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  have hne : ∀ t ∈ Icc a b, h t ≠ 0 := fun t ht ↦ Complex.slitPlane_ne_zero (hh_slit t ht)
  have heq' : Set.EqOn (fun t ↦ deriv g t / g t) (fun t ↦ deriv h t / h t) (uIoo a b) := by
    intro t ht
    rw [uIoo_of_le hab] at ht
    simp only [heq ht, heq.deriv isOpen_Ioo ht]
  have hint : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b :=
    ((hh_deriv_cont.div hh_cont hne).mono (hu ▸ Set.Subset.rfl)).intervalIntegrable
  refine ⟨hint.congr_uIoo fun t ht ↦ (heq' ht).symm, ?_⟩
  calc ∫ t in a..b, deriv g t / g t
      = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_uIoo heq'
    _ = Complex.log (h b) - Complex.log (h a) :=
        Contour.integral_deriv_div_eq_log_sub_log countable_empty (hu ▸ hh_cont)
          (fun t ht ↦ (hh_diff t (by
            rw [min_eq_left hab, max_eq_right hab] at ht
            exact ht.1)).hasDerivAt)
          (fun t ht ↦ hh_slit t (hu ▸ ht)) hint
    _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]


/-- The right-vertical piece `[0, 1]` of the telescope at `ρ`. -/
private lemma telescope_rho_piece_right_vertical (H : ℝ) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume 0 1 ∧
    ∫ t in (0 : ℝ)..1,
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H 1 - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H 0 - (UpperHalfPlane.ρ : ℂ)) := by
  have heval : ∀ s ∈ Icc (0 : ℝ) 1, fdBoundary H s = fdBoundary_segment1 H s := fun s hs ↦
    fdBoundary_of_le_one hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment1 H s - (UpperHalfPlane.ρ : ℂ)) =
      fun _ ↦ (UpperHalfPlane.ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment1]
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ))
    (h := fun s ↦ fdBoundary_segment1 H s - (UpperHalfPlane.ρ : ℂ)) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment1 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment1 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ fdBoundary_sub_rho_mem_slitPlane_of_le_one H ht)
    (fun t ht ↦ congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 0 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 1 (right_mem_Icc.mpr (by norm_num))))

/-- The first arc piece `[1, 2]` of the telescope at `ρ`. -/
private lemma telescope_rho_piece_arc_first (H : ℝ) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume 1 2 ∧
    ∫ t in (1 : ℝ)..2,
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H 2 - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H 1 - (UpperHalfPlane.ρ : ℂ)) := by
  have heval : ∀ s ∈ Icc (1 : ℝ) 2, fdBoundary H s = fdBoundary_segment2 s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · rw [← h1, fdBoundary_apply_one, fdBoundary_segment2_apply_one]
    · exact fdBoundary_of_le_two h1 hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment2 s - (UpperHalfPlane.ρ : ℂ)) = fun s ↦
      (Real.pi / 2 - Real.pi / 3) •
        (circleMap 0 1 (Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment2]
  have hθc : Continuous fun s : ℝ ↦ Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3) := by
    fun_prop
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ))
    (h := fun s ↦ fdBoundary_segment2 s - (UpperHalfPlane.ρ : ℂ)) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment2 s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment2 t).differentiableAt.sub_const _)
    (by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (Real.pi / 2 - Real.pi / 3)).continuousOn)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_rho_arc_mem_slitPlane_of_lt_three H ht.1 (by linarith [ht.2]))
    (fun t ht ↦ congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 1 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 2 (right_mem_Icc.mpr (by norm_num))))

/-- The second arc piece `[2, 3-δ_L]` of the telescope at `ρ`, stopping short of the
corner. -/
private lemma telescope_rho_piece_arc_second (H : ℝ) (hδL : 0 < δL) (hδL1 : δL < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume 2 (3 - δL) ∧
    ∫ t in (2 : ℝ)..(3 - δL),
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H (3 - δL) - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H 2 - (UpperHalfPlane.ρ : ℂ)) := by
  have hab : (2 : ℝ) ≤ 3 - δL := by linarith
  have heval : ∀ s ∈ Icc (2 : ℝ) (3 - δL), fdBoundary H s = fdBoundary_segment3 s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h2 | h2
    · rw [← h2, fdBoundary_apply_two, fdBoundary_segment3_apply_two]
    · exact fdBoundary_of_le_three h2 (by linarith [hs.2])
  have hd : deriv (fun s ↦ fdBoundary_segment3 s - (UpperHalfPlane.ρ : ℂ)) = fun s ↦
      (2 * Real.pi / 3 - Real.pi / 2) •
        (circleMap 0 1 (Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) *
          Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment3]
  have hθc : Continuous fun s : ℝ ↦
      Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2) := by
    fun_prop
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ))
    (h := fun s ↦ fdBoundary_segment3 s - (UpperHalfPlane.ρ : ℂ)) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment3 s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment3 t).differentiableAt.sub_const _)
    (by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (2 * Real.pi / 3 - Real.pi / 2)).continuousOn)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_rho_arc_mem_slitPlane_of_lt_three H (by linarith [ht.1])
        (by linarith [ht.2]))
    (fun t ht ↦ congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 2 (left_mem_Icc.mpr hab)))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval (3 - δL) (right_mem_Icc.mpr hab)))

/-- The left-vertical piece `[3+δ_R, 4]` of the telescope at `ρ`, starting past the
corner. -/
private lemma telescope_rho_piece_left_vertical (hH : Real.sqrt 3 / 2 < H) (hδR : 0 < δR)
    (hδR1 : δR ≤ 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume (3 + δR) 4 ∧
    ∫ t in (3 + δR : ℝ)..4,
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H 4 - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H (3 + δR) - (UpperHalfPlane.ρ : ℂ)) := by
  have hab : (3 + δR : ℝ) ≤ 4 := by linarith
  have heval : ∀ s ∈ Icc (3 + δR : ℝ) 4, fdBoundary H s = fdBoundary_segment4 H s :=
    fun s hs ↦ fdBoundary_of_le_four (by linarith [hs.1]) hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment4 H s - (UpperHalfPlane.ρ : ℂ)) =
      fun _ ↦ -1 / 2 + H * Complex.I - (UpperHalfPlane.ρ : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment4]
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ))
    (h := fun s ↦ fdBoundary_segment4 H s - (UpperHalfPlane.ρ : ℂ)) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment4 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment4 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_rho_mem_slitPlane_of_three_lt hH (by linarith [ht.1]) ht.2)
    (fun t ht ↦ congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval (3 + δR) (left_mem_Icc.mpr hab)))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 4 (right_mem_Icc.mpr hab)))

/-- The ceiling piece `[4, 5]` of the telescope at `ρ`. -/
private lemma telescope_rho_piece_ceiling (hH : Real.sqrt 3 / 2 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume 4 5 ∧
    ∫ t in (4 : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H 5 - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H 4 - (UpperHalfPlane.ρ : ℂ)) := by
  have heval : ∀ s ∈ Icc (4 : ℝ) 5, fdBoundary H s = fdBoundary_segment5 H s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h4 | h4
    · rw [← h4, fdBoundary_apply_four, fdBoundary_segment5_apply_four]
    · exact fdBoundary_of_gt_four h4
  have hd : deriv (fun s ↦ fdBoundary_segment5 H s - (UpperHalfPlane.ρ : ℂ)) =
      fun _ ↦ (1 : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment5]
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ))
    (h := fun s ↦ fdBoundary_segment5 H s - (UpperHalfPlane.ρ : ℂ)) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment5 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment5 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ fdBoundary_sub_rho_mem_slitPlane_of_mem_Icc_four_five hH ht)
    (fun t ht ↦ congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 4 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 5 (right_mem_Icc.mpr (by norm_num))))

/-- **The logarithmic telescope at `ρ`**: over the corner-excluded ranges the
logarithmic integral of the shifted contour is integrable and evaluates to the
difference of the endpoint logarithms beside the corner — no branch crossing occurs. -/
theorem ftc_logDeriv_telescope_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) {δL δR : ℝ}
    (hδL : 0 < δL) (hδL1 : δL < 1) (hδR : 0 < δR) (hδR1 : δR ≤ 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume 0 (3 - δL) ∧
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume (3 + δR) 5 ∧
    (∫ t in (0 : ℝ)..(3 - δL),
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))) +
      (∫ t in (3 + δR : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))) =
      Complex.log (fdBoundary H (3 - δL) - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H (3 + δR) - (UpperHalfPlane.ρ : ℂ)) := by
  obtain ⟨hi01, he01⟩ := telescope_rho_piece_right_vertical H
  obtain ⟨hi12, he12⟩ := telescope_rho_piece_arc_first H
  obtain ⟨hi23, he23⟩ := telescope_rho_piece_arc_second H hδL hδL1
  obtain ⟨hi34, he34⟩ := telescope_rho_piece_left_vertical hH hδR hδR1
  obtain ⟨hi45, he45⟩ := telescope_rho_piece_ceiling hH
  have hint02 := hi01.trans hi12
  refine ⟨hint02.trans hi23, hi34.trans hi45, ?_⟩
  have hlog50 : Complex.log (fdBoundary H 5 - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H 0 - (UpperHalfPlane.ρ : ℂ)) := by
    rw [fdBoundary_apply_five, fdBoundary_apply_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint02 hi23,
    ← intervalIntegral.integral_add_adjacent_intervals hi01 hi12,
    ← intervalIntegral.integral_add_adjacent_intervals hi34 hi45,
    he01, he12, he23, he34, he45, hlog50]
  ring

end ModularForm

end TauCeti

end
