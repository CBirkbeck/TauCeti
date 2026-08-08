/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.RhoOneGeometry

import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The logarithmic telescope of the shifted contour at `ρ + 1`

Over the corner-excluded parameter ranges `[0, 1-δ_L]` and `[1+δ_R, 5]`, the logarithmic
integral of the shifted contour `t ↦ fdBoundary H t - (ρ + 1)` telescopes through the
logarithmic FTC piece by piece. The shifted contour touches the branch cut at `t = 3`
with value `-1` while staying in the closed upper half-plane, so the two pieces meeting
there use the boundary-tolerant upper form; the principal logarithms at the touch cancel
in the telescope, and the value is exactly the difference of the two endpoint logarithms
beside the corner.

## Main declarations

* `TauCeti.ModularForm.ftc_logDeriv_telescope_rho_one` (the telescope; the analytic core
  of the generalized winding number `-1/6` at `ρ + 1`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/RhoPlusOne.lean`) this file
  ports onto the current Mathlib pin.
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


/-- The right-vertical piece `[0, 1-δ_L]` of the telescope at `ρ + 1`, stopping short of
the corner. -/
private lemma telescope_rho_one_piece_right_vertical (hH : Real.sqrt 3 / 2 < H)
    (hδL : 0 < δL) (hδL1 : δL ≤ 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume 0 (1 - δL) ∧
    ∫ t in (0 : ℝ)..(1 - δL),
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H (1 - δL) - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H 0 - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  have hab : (0 : ℝ) ≤ 1 - δL := by linarith
  have heval : ∀ s ∈ Icc (0 : ℝ) (1 - δL), fdBoundary H s = fdBoundary_segment1 H s :=
    fun s hs ↦ fdBoundary_of_le_one (by linarith [hs.2])
  have hd : deriv (fun s ↦ fdBoundary_segment1 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      fun _ ↦ (UpperHalfPlane.ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment1]
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))
    (h := fun s ↦ fdBoundary_segment1 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment1 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment1 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ (by
      refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      rw [fdBoundary_sub_rho_one_of_mem_Icc_zero_one H ⟨ht.1, by linarith [ht.2]⟩]
      have him : ((((1 - t) * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I).im =
          (1 - t) * (H - Real.sqrt 3 / 2) := by simp
      rw [him]
      have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
      positivity))
    (fun t ht ↦ congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 0 (left_mem_Icc.mpr hab)))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval (1 - δL) (right_mem_Icc.mpr hab)))

/-- The first arc piece `[1+δ_R, 2]` of the telescope at `ρ + 1`, starting past the
corner. -/
private lemma telescope_rho_one_piece_arc_first (H : ℝ) (hδR : 0 < δR) (hδR1 : δR < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume (1 + δR) 2 ∧
    ∫ t in (1 + δR : ℝ)..2,
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H 2 - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H (1 + δR) - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  have hab : (1 + δR : ℝ) ≤ 2 := by linarith
  have heval : ∀ s ∈ Icc (1 + δR : ℝ) 2, fdBoundary H s = fdBoundary_segment2 s :=
    fun s hs ↦ fdBoundary_of_le_two (by linarith [hs.1]) hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment2 s - ((UpperHalfPlane.ρ : ℂ) + 1)) = fun s ↦
      (Real.pi / 2 - Real.pi / 3) •
        (circleMap 0 1 (Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment2]
  have hθc : Continuous fun s : ℝ ↦ Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3) := by
    fun_prop
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))
    (h := fun s ↦ fdBoundary_segment2 s - ((UpperHalfPlane.ρ : ℂ) + 1)) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment2 s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment2 t).differentiableAt.sub_const _)
    (by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (Real.pi / 2 - Real.pi / 3)).continuousOn)
    (fun t ht ↦ heval t ht ▸ Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt
      (im_fdBoundary_sub_rho_one_arc_pos H (by linarith [ht.1]) (by linarith [ht.2])))))
    (fun t ht ↦ congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval (1 + δR) (left_mem_Icc.mpr hab)))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 2 (right_mem_Icc.mpr hab)))

/-- The second arc piece `[2, 3]` of the telescope at `ρ + 1`: the shifted contour meets
the branch cut at the right endpoint, so the boundary-tolerant upper form applies. -/
private lemma telescope_rho_one_piece_arc_second (H : ℝ) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume 2 3 ∧
    ∫ t in (2 : ℝ)..3,
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H 3 - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H 2 - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  have heval : ∀ s ∈ Icc (2 : ℝ) 3, fdBoundary H s = fdBoundary_segment3 s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h2 | h2
    · rw [← h2, fdBoundary_apply_two, fdBoundary_segment3_apply_two]
    · exact fdBoundary_of_le_three h2 hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment3 s - ((UpperHalfPlane.ρ : ℂ) + 1)) = fun s ↦
      (2 * Real.pi / 3 - Real.pi / 2) •
        (circleMap 0 1 (Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) *
          Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment3]
  have hθc : Continuous fun s : ℝ ↦
      Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2) := by
    fun_prop
  have hne : ∀ t ∈ Icc (2 : ℝ) 3, fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1) ≠ 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h3 | h3
    · rw [h3, fdBoundary_sub_rho_one_apply_three]
      norm_num
    · have him := im_fdBoundary_sub_rho_one_arc_pos H (by linarith [ht.1]) h3
      exact fun h0 ↦ by rw [h0] at him; simp at him
  have hu : uIcc (2 : ℝ) 3 = Icc 2 3 := uIcc_of_le (by norm_num)
  have ho : Ioo (min (2 : ℝ) 3) (max (2 : ℝ) 3) = Ioo 2 3 := by
    rw [min_eq_left (by norm_num : (2 : ℝ) ≤ 3), max_eq_right (by norm_num : (2 : ℝ) ≤ 3)]
  have hcont : ContinuousOn (fun s ↦ fdBoundary_segment3 s - ((UpperHalfPlane.ρ : ℂ) + 1))
      (Icc (2 : ℝ) 3) :=
    Continuous.continuousOn (Differentiable.continuous fun s ↦
      (hasDerivAt_fdBoundary_segment3 s).differentiableAt.sub_const _)
  have hne' : ∀ t ∈ Icc (2 : ℝ) 3,
      fdBoundary_segment3 t - ((UpperHalfPlane.ρ : ℂ) + 1) ≠ 0 := fun t ht ↦
    heval t ht ▸ hne t ht
  have hint : IntervalIntegrable (fun t ↦
      deriv (fun s ↦ fdBoundary_segment3 s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary_segment3 t - ((UpperHalfPlane.ρ : ℂ) + 1))) volume 2 3 :=
    ((((by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (2 * Real.pi / 3 - Real.pi / 2)).continuousOn :
        ContinuousOn (deriv fun s ↦ fdBoundary_segment3 s - ((UpperHalfPlane.ρ : ℂ) + 1))
          (Icc (2 : ℝ) 3))).div hcont hne').mono (hu ▸ Set.Subset.rfl)).intervalIntegrable
  exact Contour.intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_of_im_nonneg
    (g := fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))
    (h := fun s ↦ fdBoundary_segment3 s - ((UpperHalfPlane.ρ : ℂ) + 1)) countable_empty
    (hu ▸ hcont)
    (fun t ht ↦ (hasDerivAt_fdBoundary_segment3 t).differentiableAt.sub_const _)
    hint
    (fun t ht ↦ by
      rw [hu] at ht
      exact heval t ht ▸ im_fdBoundary_sub_rho_one_arc_nonneg H ⟨by linarith [ht.1], ht.2⟩)
    (hne' 2 (left_mem_Icc.mpr (by norm_num)))
    (hne' 3 (right_mem_Icc.mpr (by norm_num)))
    (fun t ht ↦ by
      rw [ho] at ht
      exact heval t ⟨ht.1.le, ht.2.le⟩ ▸ Complex.mem_slitPlane_iff.mpr (Or.inr
        (ne_of_gt (im_fdBoundary_sub_rho_one_arc_pos H (by linarith [ht.1]) ht.2))))
    (fun t ht ↦ by
      rw [ho] at ht
      exact congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 2 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 3 (right_mem_Icc.mpr (by norm_num))))

/-- The left-vertical piece `[3, 4]` of the telescope at `ρ + 1`: the shifted contour
leaves the branch cut at the left endpoint, so the boundary-tolerant upper form
applies. -/
private lemma telescope_rho_one_piece_left_vertical (hH : Real.sqrt 3 / 2 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume 3 4 ∧
    ∫ t in (3 : ℝ)..4,
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H 4 - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H 3 - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  have heval : ∀ s ∈ Icc (3 : ℝ) 4, fdBoundary H s = fdBoundary_segment4 H s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h3 | h3
    · rw [← h3, fdBoundary_apply_three, fdBoundary_segment4_apply_three]
    · exact fdBoundary_of_le_four h3 hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment4 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      fun _ ↦ -1 / 2 + H * Complex.I - (UpperHalfPlane.ρ : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment4]
  have him : ∀ t ∈ Icc (3 : ℝ) 4,
      (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).im =
        (t - 3) * (H - Real.sqrt 3 / 2) := fun t ht ↦ by
    rw [fdBoundary_sub_rho_one_of_mem_Icc_three_four H ht]
    simp
  have hne : ∀ t ∈ Icc (3 : ℝ) 4, fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1) ≠ 0 := by
    intro t ht h0
    have hre : (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).re = -1 := by
      rw [fdBoundary_sub_rho_one_of_mem_Icc_three_four H ht]
      simp
    rw [h0] at hre
    norm_num at hre
  have hu : uIcc (3 : ℝ) 4 = Icc 3 4 := uIcc_of_le (by norm_num)
  have ho : Ioo (min (3 : ℝ) 4) (max (3 : ℝ) 4) = Ioo 3 4 := by
    rw [min_eq_left (by norm_num : (3 : ℝ) ≤ 4), max_eq_right (by norm_num : (3 : ℝ) ≤ 4)]
  have hcont : ContinuousOn (fun s ↦ fdBoundary_segment4 H s - ((UpperHalfPlane.ρ : ℂ) + 1))
      (Icc (3 : ℝ) 4) :=
    Continuous.continuousOn (Differentiable.continuous fun s ↦
      (hasDerivAt_fdBoundary_segment4 H s).differentiableAt.sub_const _)
  have hne' : ∀ t ∈ Icc (3 : ℝ) 4,
      fdBoundary_segment4 H t - ((UpperHalfPlane.ρ : ℂ) + 1) ≠ 0 := fun t ht ↦
    heval t ht ▸ hne t ht
  have hint : IntervalIntegrable (fun t ↦
      deriv (fun s ↦ fdBoundary_segment4 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary_segment4 H t - ((UpperHalfPlane.ρ : ℂ) + 1))) volume 3 4 :=
    ((((by rw [hd]; exact continuousOn_const :
        ContinuousOn (deriv fun s ↦ fdBoundary_segment4 H s - ((UpperHalfPlane.ρ : ℂ) + 1))
          (Icc (3 : ℝ) 4))).div hcont hne').mono (hu ▸ Set.Subset.rfl)).intervalIntegrable
  exact Contour.intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_of_im_nonneg
    (g := fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))
    (h := fun s ↦ fdBoundary_segment4 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) countable_empty
    (hu ▸ hcont)
    (fun t ht ↦ (hasDerivAt_fdBoundary_segment4 H t).differentiableAt.sub_const _)
    hint
    (fun t ht ↦ by
      rw [hu] at ht
      exact heval t ht ▸ (by
        rw [him t ht]
        exact mul_nonneg (by linarith [ht.1]) (by linarith)))
    (hne' 3 (left_mem_Icc.mpr (by norm_num)))
    (hne' 4 (right_mem_Icc.mpr (by norm_num)))
    (fun t ht ↦ by
      rw [ho] at ht
      exact heval t ⟨ht.1.le, ht.2.le⟩ ▸ Complex.mem_slitPlane_iff.mpr (Or.inr (by
        rw [him t ⟨ht.1.le, ht.2.le⟩]
        have := mul_pos (by linarith [ht.1] : (0 : ℝ) < t - 3) (by linarith :
          (0 : ℝ) < H - Real.sqrt 3 / 2)
        linarith)))
    (fun t ht ↦ by
      rw [ho] at ht
      exact congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 3 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 4 (right_mem_Icc.mpr (by norm_num))))

/-- The ceiling piece `[4, 5]` of the telescope at `ρ + 1`. -/
private lemma telescope_rho_one_piece_ceiling (hH : Real.sqrt 3 / 2 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume 4 5 ∧
    ∫ t in (4 : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H 5 - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H 4 - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  have heval : ∀ s ∈ Icc (4 : ℝ) 5, fdBoundary H s = fdBoundary_segment5 H s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h4 | h4
    · rw [← h4, fdBoundary_apply_four, fdBoundary_segment5_apply_four]
    · exact fdBoundary_of_gt_four h4
  have hd : deriv (fun s ↦ fdBoundary_segment5 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      fun _ ↦ (1 : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment5]
  have hslit : ∀ t ∈ Icc (4 : ℝ) 5,
      fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1) ∈ Complex.slitPlane := by
    intro t ht
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    have him : (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).im =
        H - Real.sqrt 3 / 2 := by
      rw [Complex.sub_im, im_fdBoundary_segment5 H ht]
      norm_num [UpperHalfPlane.ρ]
    rw [him]
    linarith
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1))
    (h := fun s ↦ fdBoundary_segment5 H s - ((UpperHalfPlane.ρ : ℂ) + 1)) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment5 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment5 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ hslit t ht)
    (fun t ht ↦ congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 4 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - ((UpperHalfPlane.ρ : ℂ) + 1)) (heval 5 (right_mem_Icc.mpr (by norm_num))))

/-- **The logarithmic telescope at `ρ + 1`**: over the corner-excluded ranges the
logarithmic integral of the shifted contour is integrable and evaluates to the
difference of the endpoint logarithms beside the corner — the branch-cut touch at
`t = 3` passes through the principal logarithm without a jump. -/
theorem ftc_logDeriv_telescope_rho_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) {δL δR : ℝ}
    (hδL : 0 < δL) (hδL1 : δL ≤ 1) (hδR : 0 < δR) (hδR1 : δR < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume 0 (1 - δL) ∧
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
        (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)))
      volume (1 + δR) 5 ∧
    (∫ t in (0 : ℝ)..(1 - δL),
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1))) +
      (∫ t in (1 + δR : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - ((UpperHalfPlane.ρ : ℂ) + 1)) t /
          (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1))) =
      Complex.log (fdBoundary H (1 - δL) - ((UpperHalfPlane.ρ : ℂ) + 1)) -
        Complex.log (fdBoundary H (1 + δR) - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
  obtain ⟨hi01, he01⟩ := telescope_rho_one_piece_right_vertical hH hδL hδL1
  obtain ⟨hi12, he12⟩ := telescope_rho_one_piece_arc_first H hδR hδR1
  obtain ⟨hi23, he23⟩ := telescope_rho_one_piece_arc_second H
  obtain ⟨hi34, he34⟩ := telescope_rho_one_piece_left_vertical hH
  obtain ⟨hi45, he45⟩ := telescope_rho_one_piece_ceiling hH
  have hint13 := hi12.trans hi23
  have hint34 := hi34.trans hi45
  refine ⟨hi01, hint13.trans hint34, ?_⟩
  have hlog50 : Complex.log (fdBoundary H 5 - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      Complex.log (fdBoundary H 0 - ((UpperHalfPlane.ρ : ℂ) + 1)) := by
    rw [fdBoundary_apply_five, fdBoundary_apply_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint13 hint34,
    ← intervalIntegral.integral_add_adjacent_intervals hi12 hi23,
    ← intervalIntegral.integral_add_adjacent_intervals hi34 hi45,
    he01, he12, he23, he34, he45, hlog50]
  ring

end ModularForm

end TauCeti

end
