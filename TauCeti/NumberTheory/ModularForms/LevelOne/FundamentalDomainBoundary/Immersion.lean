/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The boundary contour is a piecewise-`C¹` immersion

Away from the three genuine corners every piece of the boundary contour has a nonvanishing
tangent: the verticals and the horizontal move with constant nonzero chords (the height
differing from the corner row keeps the verticals nondegenerate), and the unified arc moves at
constant speed `π/6`. This is the regularity that feeds the principal-value existence of
the winding decomposition and the residue sum along the contour.

## Main declarations

* `TauCeti.ModularForm.isPwC1ImmersionOn_fdBoundary`.
-/

public noncomputable section

open Complex Set UpperHalfPlane TauCeti.Contour

open scoped Real

namespace TauCeti

namespace ModularForm

variable {H t c d : ℝ}

-- Duplicated from `Basic` deliberately: review guidance keeps the interval classification
-- private on both sides rather than public API.
private lemma subset_piece_of_disjoint_corners {c d : ℝ} (hcd : Icc c d ⊆ Icc (0 : ℝ) 5)
    (hdis : Disjoint (fdBoundaryCorners : Set ℝ) (Ioo c d)) :
    Icc c d ⊆ Icc (0 : ℝ) 1 ∨ Icc c d ⊆ Icc (1 : ℝ) 3 ∨ Icc c d ⊆ Icc (3 : ℝ) 4 ∨
      Icc c d ⊆ Icc (4 : ℝ) 5 := by
  have hbp : ∀ m : ℝ, m ∈ fdBoundaryCorners → m ∉ Ioo c d := fun m hm ↦
    Set.disjoint_left.mp hdis (Finset.mem_coe.mpr hm)
  rcases le_or_gt d 1 with hd1 | hd1
  · exact Or.inl fun x hx ↦ ⟨(hcd hx).1, hx.2.trans hd1⟩
  · have hc1 : 1 ≤ c := le_of_not_gt fun hlt ↦ hbp 1 (by simp) ⟨hlt, hd1⟩
    rcases le_or_gt d 3 with hd3 | hd3
    · exact Or.inr (Or.inl fun x hx ↦ ⟨hc1.trans hx.1, hx.2.trans hd3⟩)
    · have hc3 : 3 ≤ c := le_of_not_gt fun hlt ↦ hbp 3 (by simp) ⟨hlt, hd3⟩
      rcases le_or_gt d 4 with hd4 | hd4
      · exact Or.inr (Or.inr (Or.inl fun x hx ↦ ⟨hc3.trans hx.1, hx.2.trans hd4⟩))
      · have hc4 : 4 ≤ c := le_of_not_gt fun hlt ↦ hbp 4 (by simp) ⟨hlt, hd4⟩
        exact Or.inr (Or.inr (Or.inr fun x hx ↦ ⟨hc4.trans hx.1, (hcd hx).2⟩))

/-- The vertical chords are nonzero exactly when the height differs from the corner row. -/
private lemma segment1_chord_ne_zero (hH : H ≠ Real.sqrt 3 / 2) :
    (ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) ≠ 0 := by
  intro h0
  apply hH
  have him : ((ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)).im = Real.sqrt 3 / 2 - H := by
    simp [ρ]
  rw [h0, Complex.zero_im] at him
  linarith

private lemma segment4_chord_ne_zero (hH : H ≠ Real.sqrt 3 / 2) :
    (-1 / 2 : ℂ) + H * Complex.I - (ρ : ℂ) ≠ 0 := by
  intro h0
  apply hH
  have him : ((-1 / 2 : ℂ) + H * Complex.I - (ρ : ℂ)).im = H - Real.sqrt 3 / 2 := by
    simp [ρ]
  rw [h0, Complex.zero_im] at him
  linarith

private lemma arc_deriv_ne_zero (t : ℝ) :
    (Real.pi / 6) • (circleMap 0 1 ((t + 1) * (Real.pi / 6)) * Complex.I) ≠ 0 := by
  refine smul_ne_zero (by positivity) (mul_ne_zero ?_ Complex.I_ne_zero)
  exact circleMap_ne_center one_ne_zero

/-- The boundary contour is a piecewise-`C¹` immersion: every corner-free piece is `C¹`
with nonvanishing tangent. -/
theorem isPwC1ImmersionOn_fdBoundary (hH : H ≠ Real.sqrt 3 / 2) :
    IsPwC1ImmersionOn (fdBoundary H) 0 5 := by
  rw [isPwC1ImmersionOn_iff]
  refine ⟨(continuous_fdBoundary H).continuousOn, fdBoundaryCorners, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_coe, mem_fdBoundaryCorners] at hx
    rw [min_eq_left (by norm_num : (0 : ℝ) ≤ 5), max_eq_right (by norm_num : (0 : ℝ) ≤ 5)]
    rcases hx with rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  · intro c d hlt hsub hdis
    have hsub' : Icc c d ⊆ Icc (0 : ℝ) 5 := by
      rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hsub
    refine ⟨contDiffOn_fdBoundary H hsub' hdis, fun t ht ↦ ?_⟩
    have h_uniq : UniqueDiffWithinAt ℝ (Icc c d) t := uniqueDiffOn_Icc hlt t ht
    rcases subset_piece_of_disjoint_corners hsub' hdis with h | h | h | h
    · rw [derivWithin_congr (fun s hs ↦ eqOn_fdBoundary_segment1 H (h hs))
        (eqOn_fdBoundary_segment1 H (h ht)),
        (hasDerivAt_fdBoundary_segment1 H t).hasDerivWithinAt.derivWithin h_uniq]
      exact segment1_chord_ne_zero hH
    · rw [(hasDerivWithinAt_fdBoundary_arc (h ⟨le_rfl, hlt.le⟩).1
        (h ⟨hlt.le, le_rfl⟩).2 ht).derivWithin h_uniq]
      exact arc_deriv_ne_zero t
    · rw [derivWithin_congr (fun s hs ↦ eqOn_fdBoundary_segment4 H (h hs))
        (eqOn_fdBoundary_segment4 H (h ht)),
        (hasDerivAt_fdBoundary_segment4 H t).hasDerivWithinAt.derivWithin h_uniq]
      exact segment4_chord_ne_zero hH
    · rw [derivWithin_congr (fun s hs ↦ eqOn_fdBoundary_segment5 H (h hs))
        (eqOn_fdBoundary_segment5 H (h ht)),
        (hasDerivAt_fdBoundary_segment5 H t).hasDerivWithinAt.derivWithin h_uniq]
      exact one_ne_zero

end ModularForm

end TauCeti

end
