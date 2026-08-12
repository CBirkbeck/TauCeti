/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Containment
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Basic
import TauCeti.Topology.Circle.Metric

/-!
# Winding of the boundary contour at its smooth non-corner points

Every point of the truncated-fundamental-domain boundary that is not one of the corner
points `ρ`, `ρ + 1`, `-1/2 + H·i`, `1/2 + H·i` is crossed smoothly by a single piece of the
contour, and the generalized winding number there is `-1/2`: half a clockwise turn, exactly
as at the elliptic point `i`. This file proves that value on the two open smooth strata —
the open vertical edges and the open unit arc — the winding weights of the boundary divisor
points in the valence formula.

The computation generalizes the route proven at `i`
(`TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_I`): a logarithmic telescope over the
`δ`-excised contour followed by the excision collapse at the chord-matched half-width. One
choice removes that file's branch-crossing bookkeeping: instead of the principal branch of
`log (γ t - w)`, the telescope runs on `log ((γ t - w) · c)` for a unit `c` rotating the
branch cut into a ray from `w` that misses the rest of the contour — `c = -1` on the right
vertical, `c = 1` on the left, `c = w⁻¹` on the arc. With the cut so aimed, the whole excised
contour is slit-plane-valued for the one branch, the telescope needs no interior crossing
corrections, and both pieces evaluate by the comparison-free logarithmic FTC.

At a vertical point the excision endpoints sit at `w ± ε·i`, so the excised integral is the
constant `-π·i`; at an arc point it is `-π·i - 2·arcsin(ε/2)·i`, the same value the collapse
at `i` produced, and the limit is `-π·i` in both cases.

The arc statement covers the whole open arc, including `i`; the specific value
`TauCeti.ModularForm.windingNumber_fdBoundary_I` stays the `simp`-normal anchor at that
closed point.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_vertical`,
  `TauCeti.ModularForm.windingNumber_fdBoundary_vertical`: the principal value `-πi` and the
  winding number `-1/2` at a point of an open vertical edge.
* `TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_arc`,
  `TauCeti.ModularForm.windingNumber_fdBoundary_arc`: the same values at a point of the open
  unit arc.

The hypotheses are spelled the way the singular-set interfaces provide them
(`TauCeti.ModularForm.verticalSingularSet`, `arcSingularSet`): a vertical point carries
`w.re = 1/2 ∨ w.re = -(1/2)`, `1 < ‖w‖`, `0 < w.im` and `w.im < H`; an arc point carries
`‖w‖ = 1`, `|w.re| < 1/2` and `0 < w.im`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  winding-weight development (`ForMathlib/ValenceFormula/WindingWeights/`) proves these
  values at the three corner points; the non-corner statements and the rotated-branch
  telescope that uniformizes them are Tau Ceti's.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

open Contour

namespace ModularForm

variable {H t t₀ s δ ε : ℝ} {w c : ℂ}

/-! ## The excised telescope for a branch adapted to the crossing point

For a unit `c` such that `(γ t - w) · c` stays in the slit plane along the whole excised
contour, the logarithmic integral over each of the two excised parameter ranges is an
endpoint-log difference for the rotated branch, and closedness cancels the shared basepoint:
the excised integral is `log ((γ(t₀-δ) - w)·c) - log ((γ(t₀+δ) - w)·c)`.
-/

/-- Off the three parameterization corners the assembled contour is differentiable. -/
private lemma hasDerivAt_fdBoundary_of_ne (h1 : t ≠ 1) (h3 : t ≠ 3) (h4 : t ≠ 4) :
    HasDerivAt (fdBoundary H) (deriv (fdBoundary H) t) t := by
  rcases lt_trichotomy t 1 with h | h | h
  · exact (hasDerivAt_fdBoundary_of_lt_one h).differentiableAt.hasDerivAt
  · exact absurd h h1
  rcases lt_trichotomy t 3 with h' | h' | h'
  · exact (hasDerivAt_fdBoundary_of_mem_Ioo_one_three ⟨h, h'⟩).differentiableAt.hasDerivAt
  · exact absurd h' h3
  rcases lt_trichotomy t 4 with h'' | h'' | h''
  · exact (hasDerivAt_fdBoundary_of_mem_Ioo_three_four ⟨h', h''⟩).differentiableAt.hasDerivAt
  · exact absurd h'' h4
  · exact (hasDerivAt_fdBoundary_of_gt_four h'').differentiableAt.hasDerivAt

/-- **The telescope piece for an adapted branch.** On a corner-tolerant parameter range
along which the shifted-and-rotated contour `(γ t - w) · c` stays in the slit plane, the
logarithmic integrand of the shifted contour is interval integrable, and its integral is the
endpoint difference of the rotated branch `log ((γ t - w) · c)`. -/
private lemma telescope_piece_of_slit_branch {a b : ℝ} (hc : c ≠ 0) (hab : a ≤ b)
    (hsub : Icc a b ⊆ Icc (0 : ℝ) 5)
    (hslit : ∀ t ∈ Icc a b, (fdBoundary H t - w) * c ∈ Complex.slitPlane) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - w) t / (fdBoundary H t - w)) volume a b ∧
    ∫ t in a..b, deriv (fun s ↦ fdBoundary H s - w) t / (fdBoundary H t - w) =
      Complex.log ((fdBoundary H b - w) * c) - Complex.log ((fdBoundary H a - w) * c) := by
  have hne : ∀ t ∈ Icc a b, fdBoundary H t ≠ w := fun t ht heq ↦
    Complex.slitPlane_ne_zero (hslit t ht) (by rw [heq, sub_self, zero_mul])
  have hint : IntervalIntegrable
      (fun t ↦ (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t) volume a b :=
    Contour.intervalIntegrable_inv_sub_mul_deriv (continuous_fdBoundary H).continuousOn
      (fun t ht ↦ hne t (by rwa [uIcc_of_le hab] at ht))
      (((isPiecewiseC1On_fdBoundary H).intervalIntegrable_deriv).mono_set
        (by rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]; exact hsub))
  have hfun : (fun t ↦ deriv (fun s ↦ fdBoundary H s - w) t * c / ((fdBoundary H t - w) * c))
      = fun t ↦ deriv (fun s ↦ fdBoundary H s - w) t / (fdBoundary H t - w) :=
    funext fun t ↦ mul_div_mul_right _ _ hc
  have hfun2 : (fun t ↦ deriv (fun s ↦ fdBoundary H s - w) t / (fdBoundary H t - w))
      = fun t ↦ (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t :=
    funext fun t ↦ by rw [deriv_sub_const, inv_mul_eq_div]
  have hdiff : ∀ t ∈ Ioo (min a b) (max a b) \ (fdBoundaryCorners : Set ℝ),
      HasDerivAt (fun s ↦ (fdBoundary H s - w) * c)
        (deriv (fun s ↦ fdBoundary H s - w) t * c) t := by
    intro t ht
    have hcor := ht.2
    rw [Finset.mem_coe, mem_fdBoundaryCorners] at hcor
    push Not at hcor
    simpa only [deriv_sub_const] using
      ((hasDerivAt_fdBoundary_of_ne hcor.1 hcor.2.1 hcor.2.2).sub_const w).mul_const c
  have hmain := Contour.integral_deriv_div_eq_log_sub_log
    (f := fun s ↦ (fdBoundary H s - w) * c)
    (f' := fun t ↦ deriv (fun s ↦ fdBoundary H s - w) t * c)
    fdBoundaryCorners.countable_toSet
    ((((continuous_fdBoundary H).sub continuous_const).mul continuous_const).continuousOn)
    hdiff (fun t ht ↦ hslit t (by rwa [uIcc_of_le hab] at ht))
    (by rw [hfun, hfun2]; exact hint)
  rw [hfun] at hmain
  exact ⟨by rw [hfun2]; exact hint, hmain⟩

/-- **The excision collapse for an adapted branch.** If beyond the excised parameter window
the contour keeps distance more than `ε` from `w` while the rotated branch stays in the slit
plane, and within the window it stays within `ε`, then the `ε`-truncated index integrand is
interval integrable over the whole contour and its integral is the window-endpoint log
difference of the rotated branch. -/
private lemma truncated_integral_spec_of_slit_branch (hc : c ≠ 0)
    (h0 : 0 ≤ t₀ - δ) (hδ : 0 < δ) (h5 : t₀ + δ ≤ 5)
    (hslit : ∀ t ∈ Icc (0 : ℝ) 5, t ∉ Ioo (t₀ - δ) (t₀ + δ) →
      (fdBoundary H t - w) * c ∈ Complex.slitPlane)
    (hfar_left : ∀ s ∈ Ioo (0 : ℝ) (t₀ - δ), ε < ‖fdBoundary H s - w‖)
    (hfar_right : ∀ s ∈ Ioo (t₀ + δ) (5 : ℝ), ε < ‖fdBoundary H s - w‖)
    (hnear : ∀ s ∈ Icc (t₀ - δ) (t₀ + δ), ‖fdBoundary H s - w‖ ≤ ε) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
      Complex.log ((fdBoundary H (t₀ - δ) - w) * c) -
        Complex.log ((fdBoundary H (t₀ + δ) - w) * c) := by
  have hab2 : t₀ - δ ≤ t₀ + δ := by linarith
  obtain ⟨hiL, heL⟩ := telescope_piece_of_slit_branch hc h0
    (Icc_subset_Icc le_rfl (by linarith)) (fun t ht ↦ hslit t ⟨ht.1, by linarith [ht.2]⟩
      fun hmem ↦ absurd ht.2 (not_le.mpr hmem.1))
  obtain ⟨hiR, heR⟩ := telescope_piece_of_slit_branch hc h5
    (Icc_subset_Icc (by linarith) le_rfl) (fun t ht ↦ hslit t ⟨by linarith [ht.1], ht.2⟩
      fun hmem ↦ absurd ht.1 (not_le.mpr hmem.2))
  have haeL := Contour.ae_logDeriv_sub_eq_truncated (γ := fdBoundary H) (z₀ := w) (ε := ε)
    h0 hfar_left
  have haeR := Contour.ae_logDeriv_sub_eq_truncated (γ := fdBoundary H) (z₀ := w) (ε := ε)
    h5 hfar_right
  obtain ⟨hiM, hM0⟩ :=
    Contour.intervalIntegrable_truncated_and_integral_truncated_eq_zero_of_norm_le
      (γ := fdBoundary H) (z₀ := w)
      (g := fun s ↦ (fdBoundary H s - w)⁻¹ * deriv (fdBoundary H) s)
      (Filter.Eventually.of_forall fun s hs ↦ hnear s
        (Ioc_subset_Icc_self (by rwa [uIoc_of_le hab2] at hs)))
  have hiL' := hiL.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr haeL)
  have hiR' := hiR.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr haeR)
  refine ⟨(hiL'.trans hiM).trans hiR', ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hiL'.trans hiM) hiR',
    ← intervalIntegral.integral_add_adjacent_intervals hiL' hiM, hM0, add_zero,
    ← intervalIntegral.integral_congr_ae haeL, ← intervalIntegral.integral_congr_ae haeR,
    heL, heR, fdBoundary_apply_five, fdBoundary_apply_zero]
  ring

/-! ## The vertical edges

A point `w` of an open vertical edge is crossed by exactly one straight segment. Along it the
shifted contour `γ t - w` is purely imaginary, so the chord distance is linear in the
parameter and the matched half-width is `δ(ε) = ε / (H - √3/2)`. The adapted branch negates
on the right edge and is the principal one on the left; either way the excision endpoints are
`±ε·i` and the excised integral is the constant `-π·i`.
-/

/-- On the right vertical the shifted contour is purely imaginary, with signed height linear
in the parameter. -/
private lemma fdBoundary_sub_of_le_one (hre : w.re = 1 / 2) (hs : s ≤ 1) :
    fdBoundary H s - w =
      ((H - w.im - s * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · rw [Complex.sub_re, re_fdBoundary_of_le_one hs, hre, Complex.mul_I_re, Complex.ofReal_im]
    norm_num
  · rw [Complex.sub_im, im_fdBoundary_of_le_one hs, Complex.mul_I_im, Complex.ofReal_re]
    ring

/-- On the left vertical the shifted contour is purely imaginary, with signed height linear
in the parameter. -/
private lemma fdBoundary_sub_of_mem_Icc_three_four (hre : w.re = -(1 / 2))
    (hs : s ∈ Icc (3 : ℝ) 4) :
    fdBoundary H s - w =
      ((Real.sqrt 3 / 2 + (s - 3) * (H - Real.sqrt 3 / 2) - w.im : ℝ) : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · rw [Complex.sub_re, re_fdBoundarySegment4 H hs, hre, Complex.mul_I_re, Complex.ofReal_im]
    norm_num
  · rw [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re]
    rcases eq_or_lt_of_le hs.1 with h3 | h3
    · rw [← h3, fdBoundary_apply_three]
      have hρ : ((UpperHalfPlane.ρ : ℂ)).im = Real.sqrt 3 / 2 := by simp [UpperHalfPlane.ρ]
      rw [hρ]
      ring
    · rw [im_fdBoundary_of_le_four h3 hs.2]

/-- For a right-vertical point, the negated branch is slit-plane-valued wherever the contour
misses `w`: the whole contour lies weakly left of the edge. -/
private lemma slit_branch_vertical_right (hre : w.re = 1 / 2) (ht : t ≤ 5)
    (hne : fdBoundary H t ≠ w) : (fdBoundary H t - w) * (-1) ∈ Complex.slitPlane := by
  have hre0 : 0 ≤ (w - fdBoundary H t).re := by
    rw [Complex.sub_re, hre]
    linarith [(abs_le.mp (abs_re_fdBoundary_le_half (H := H) ht)).2]
  rw [mul_neg_one, neg_sub, Complex.mem_slitPlane_iff]
  rcases eq_or_ne (w - fdBoundary H t).im 0 with him0 | him0
  · rcases lt_or_eq_of_le hre0 with h | h
    · exact Or.inl h
    · refine absurd (sub_eq_zero.mp ?_).symm hne
      exact Complex.ext (by simpa using h.symm) (by simpa using him0)
  · exact Or.inr him0

/-- For a left-vertical point, the principal branch is slit-plane-valued wherever the contour
misses `w`: the whole contour lies weakly right of the edge. -/
private lemma slit_branch_vertical_left (hre : w.re = -(1 / 2)) (ht : t ≤ 5)
    (hne : fdBoundary H t ≠ w) : fdBoundary H t - w ∈ Complex.slitPlane := by
  have hre0 : 0 ≤ (fdBoundary H t - w).re := by
    rw [Complex.sub_re, hre]
    linarith [(abs_le.mp (abs_re_fdBoundary_le_half (H := H) ht)).1]
  rw [Complex.mem_slitPlane_iff]
  rcases eq_or_ne (fdBoundary H t - w).im 0 with him0 | him0
  · rcases lt_or_eq_of_le hre0 with h | h
    · exact Or.inl h
    · refine absurd (sub_eq_zero.mp ?_) hne
      exact Complex.ext (by simpa using h.symm) (by simpa using him0)
  · exact Or.inr him0

/-- The endpoint-log difference shared by both vertical edges: the two excision endpoints
of a straight crossing sit at `∓ε·i` for the adapted branch, and their logarithms differ by
the straight angle `-π·i` — the log-norm parts cancel exactly. -/
private lemma log_neg_eps_I_sub_log_eps_I (hε : 0 < ε) :
    Complex.log (((-ε : ℝ) : ℂ) * Complex.I) - Complex.log ((ε : ℂ) * Complex.I) =
      -(Real.pi : ℂ) * Complex.I := by
  rw [show ((-ε : ℝ) : ℂ) * Complex.I = (ε : ℂ) * -Complex.I by push_cast; ring,
    Complex.log_ofReal_mul hε (neg_ne_zero.mpr Complex.I_ne_zero),
    Complex.log_ofReal_mul hε Complex.I_ne_zero, Complex.log_neg_I, Complex.log_I]
  ring

/-- The contour meets a right-vertical point only at the crossing parameter
`t₀ = (H - w.im) / (H - √3/2)`. -/
private lemma fdBoundary_ne_right (hre : w.re = 1 / 2) (hnorm : 1 < ‖w‖)
    (him_lo : Real.sqrt 3 / 2 < w.im) (himH : w.im < H)
    (hts : t ≠ (H - w.im) / (H - Real.sqrt 3 / 2)) : fdBoundary H t ≠ w := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  intro heq
  rcases le_or_gt t 1 with h1 | h1
  · have hI := fdBoundary_sub_of_le_one (H := H) hre h1
    rw [heq, sub_self] at hI
    have h0 : H - w.im - t * (H - Real.sqrt 3 / 2) = 0 := by
      simpa using congrArg Complex.im hI.symm
    refine hts ?_
    rw [eq_div_iff hk.ne']
    linarith
  · rcases le_or_gt t 3 with h3 | h3
    · have hn := norm_fdBoundary_arc (H := H) h1.le h3
      rw [heq] at hn
      linarith
    · rcases le_or_gt t 4 with h4 | h4
      · have hr := re_fdBoundarySegment4 H ⟨h3.le, h4⟩
        rw [heq, hre] at hr
        norm_num at hr
      · have hi := im_fdBoundary_of_gt_four (H := H) h4
        rw [heq] at hi
        linarith

/-- The contour meets a left-vertical point only at the crossing parameter
`t₀ = 3 + (w.im - √3/2) / (H - √3/2)`. -/
private lemma fdBoundary_ne_left (hre : w.re = -(1 / 2)) (hnorm : 1 < ‖w‖)
    (him_lo : Real.sqrt 3 / 2 < w.im) (himH : w.im < H)
    (hts : t ≠ 3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)) :
    fdBoundary H t ≠ w := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  intro heq
  rcases le_or_gt t 1 with h1 | h1
  · have hr := re_fdBoundary_of_le_one (H := H) h1
    rw [heq, hre] at hr
    norm_num at hr
  · rcases le_or_gt t 3 with h3 | h3
    · have hn := norm_fdBoundary_arc (H := H) h1.le h3
      rw [heq] at hn
      linarith
    · rcases le_or_gt t 4 with h4 | h4
      · have hI := fdBoundary_sub_of_mem_Icc_three_four (H := H) hre ⟨h3.le, h4⟩
        rw [heq, sub_self] at hI
        have h0 : Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) - w.im = 0 := by
          simpa using congrArg Complex.im hI.symm
        refine hts ?_
        have hdiv : t - 3 = (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) := by
          rw [eq_div_iff hk.ne']
          linarith
        linarith
      · have hi := im_fdBoundary_of_gt_four (H := H) h4
        rw [heq] at hi
        linarith

/-- Away from the right vertical, the contour keeps its distance from a right-vertical
point: at least `1` on the opposite vertical, `‖w‖ - 1` on the arc, and `H - w.im` on the
ceiling. -/
private lemma lt_norm_sub_right_of_off_segment (hre : w.re = 1 / 2)
    (hε₁ : ε < 1) (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (h1 : 1 ≤ s)
    (h5 : s ≤ 5) : ε < ‖fdBoundary H s - w‖ := by
  rcases le_or_gt s 3 with h3 | h3
  · calc ε < ‖w‖ - ‖fdBoundary H s‖ := by rw [norm_fdBoundary_arc h1 h3]; linarith
      _ ≤ ‖w - fdBoundary H s‖ := norm_sub_norm_le _ _
      _ = ‖fdBoundary H s - w‖ := norm_sub_rev _ _
  · rcases le_or_gt s 4 with h4 | h4
    · have hr : (fdBoundary H s - w).re = -1 := by
        rw [Complex.sub_re, re_fdBoundarySegment4 H ⟨h3.le, h4⟩, hre]
        norm_num
      calc ε < 1 := hε₁
        _ = |(fdBoundary H s - w).re| := by rw [hr]; norm_num
        _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_re_le_norm _
    · have hi : (fdBoundary H s - w).im = H - w.im := by
        rw [Complex.sub_im, im_fdBoundarySegment5 H ⟨h4.le, h5⟩]
      calc ε < H - w.im := hεc
        _ ≤ |(fdBoundary H s - w).im| := by rw [hi]; exact le_abs_self _
        _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_im_le_norm _

/-- Away from the left vertical, the contour keeps its distance from a left-vertical point:
at least `1` on the opposite vertical, `‖w‖ - 1` on the arc, and `H - w.im` on the
ceiling. -/
private lemma lt_norm_sub_left_of_off_segment (hre : w.re = -(1 / 2))
    (hε₁ : ε < 1) (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (hs : s ∈ Icc (0 : ℝ) 5)
    (hoff : s ≤ 3 ∨ 4 ≤ s) : ε < ‖fdBoundary H s - w‖ := by
  rcases hoff with h3 | h4
  · rcases le_or_gt s 1 with h1 | h1
    · have hr : (fdBoundary H s - w).re = 1 := by
        rw [Complex.sub_re, re_fdBoundary_of_le_one h1, hre]
        norm_num
      calc ε < 1 := hε₁
        _ = |(fdBoundary H s - w).re| := by rw [hr]; norm_num
        _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_re_le_norm _
    · calc ε < ‖w‖ - ‖fdBoundary H s‖ := by rw [norm_fdBoundary_arc h1.le h3]; linarith
        _ ≤ ‖w - fdBoundary H s‖ := norm_sub_norm_le _ _
        _ = ‖fdBoundary H s - w‖ := norm_sub_rev _ _
  · have hi : (fdBoundary H s - w).im = H - w.im := by
      rw [Complex.sub_im, im_fdBoundarySegment5 H ⟨h4, hs.2⟩]
    calc ε < H - w.im := hεc
      _ ≤ |(fdBoundary H s - w).im| := by rw [hi]; exact le_abs_self _
      _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_im_le_norm _

/-- The norm of the shifted contour along the right vertical, in linear form. -/
private lemma norm_fdBoundary_sub_of_le_one (hre : w.re = 1 / 2) (hs : s ≤ 1) :
    ‖fdBoundary H s - w‖ = |H - w.im - s * (H - Real.sqrt 3 / 2)| := by
  rw [fdBoundary_sub_of_le_one hre hs, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- **The window of a right-vertical crossing**: the chord-matched window around the
crossing parameter sits inside the open segment range, and its endpoints are exactly
`w ± ε·i`. -/
private lemma right_window_endpoints (hre : w.re = 1 / 2) (hε : 0 < ε)
    (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    0 < (H - w.im) / (H - Real.sqrt 3 / 2) - ε / (H - Real.sqrt 3 / 2) ∧
    (H - w.im) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2) < 1 ∧
    fdBoundary H ((H - w.im) / (H - Real.sqrt 3 / 2) - ε / (H - Real.sqrt 3 / 2)) - w =
      (ε : ℂ) * Complex.I ∧
    fdBoundary H ((H - w.im) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2)) - w =
      ((-ε : ℝ) : ℂ) * Complex.I := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hδpos : 0 < ε / (H - Real.sqrt 3 / 2) := div_pos hε hk
  have ht₀k : (H - w.im) / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = H - w.im :=
    div_mul_cancel₀ _ hk.ne'
  have hδk : ε / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ _ hk.ne'
  have hwl : 0 < (H - w.im) / (H - Real.sqrt 3 / 2) - ε / (H - Real.sqrt 3 / 2) := by
    rw [← sub_div]
    exact div_pos (by linarith) hk
  have hwr : (H - w.im) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2) < 1 := by
    rw [← add_div, div_lt_one hk]
    linarith
  refine ⟨hwl, hwr, ?_, ?_⟩ <;> rw [fdBoundary_sub_of_le_one hre (by linarith [hwr])]
  · exact congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) (by rw [sub_mul]; linarith)
  · exact congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) (by rw [add_mul]; linarith)

/-- **The distance bounds of a right-vertical crossing**: beyond the chord-matched window
the contour keeps distance more than `ε` from `w`, and within it at most `ε`. -/
private lemma right_window_bounds (hre : w.re = 1 / 2) (hε : 0 < ε) (hε₁ : ε < 1)
    (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    (∀ s ∈ Ioo (0 : ℝ) ((H - w.im) / (H - Real.sqrt 3 / 2) - ε / (H - Real.sqrt 3 / 2)),
      ε < ‖fdBoundary H s - w‖) ∧
    (∀ s ∈ Ioo ((H - w.im) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2)) (5 : ℝ),
      ε < ‖fdBoundary H s - w‖) ∧
    ∀ s ∈ Icc ((H - w.im) / (H - Real.sqrt 3 / 2) - ε / (H - Real.sqrt 3 / 2))
      ((H - w.im) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2)),
      ‖fdBoundary H s - w‖ ≤ ε := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hδpos : 0 < ε / (H - Real.sqrt 3 / 2) := div_pos hε hk
  obtain ⟨hwl, hwr, -, -⟩ := right_window_endpoints hre hε hεc hεv
  have ht₀k : (H - w.im) / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = H - w.im :=
    div_mul_cancel₀ _ hk.ne'
  have hδk : ε / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ _ hk.ne'
  refine ⟨fun s hs ↦ ?_, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · have hlt := mul_lt_mul_of_pos_right hs.2 hk
    rw [sub_mul, ht₀k, hδk] at hlt
    rw [norm_fdBoundary_sub_of_le_one hre (by linarith [hs.2, hwr])]
    exact lt_of_lt_of_le
      (show ε < H - w.im - s * (H - Real.sqrt 3 / 2) by linarith) (le_abs_self _)
  · rcases le_or_gt s 1 with h1 | h1
    · have hlt := mul_lt_mul_of_pos_right hs.1 hk
      rw [add_mul, ht₀k, hδk] at hlt
      rw [norm_fdBoundary_sub_of_le_one hre h1]
      exact lt_of_lt_of_le
        (show ε < -(H - w.im - s * (H - Real.sqrt 3 / 2)) by linarith) (neg_le_abs _)
    · exact lt_norm_sub_right_of_off_segment hre hε₁ hεa hεc h1.le hs.2.le
  · have hl := mul_le_mul_of_nonneg_right hs.1 hk.le
    have hr := mul_le_mul_of_nonneg_right hs.2 hk.le
    rw [sub_mul, ht₀k, hδk] at hl
    rw [add_mul, ht₀k, hδk] at hr
    rw [norm_fdBoundary_sub_of_le_one hre (by linarith [hs.2, hwr])]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The excision collapse at a right-vertical point**: for small `ε`, the `ε`-excised
index integrand of the boundary contour about `w` is interval integrable, and its integral
is exactly `-πi` — the excision endpoints are `w ± ε·i` and the log-norm parts cancel. -/
private lemma truncated_integral_spec_right (hre : w.re = 1 / 2)
    (him_lo : Real.sqrt 3 / 2 < w.im) (himH : w.im < H) (hε : 0 < ε) (hε₁ : ε < 1)
    (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
      -(Real.pi : ℂ) * Complex.I := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hδpos : 0 < ε / (H - Real.sqrt 3 / 2) := div_pos hε hk
  obtain ⟨hwl, hwr, hL, hR⟩ := right_window_endpoints hre hε hεc hεv
  obtain ⟨hfl, hfr, hnear⟩ := right_window_bounds hre hε hε₁ hεa hεc hεv
  obtain ⟨hint, hval⟩ := truncated_integral_spec_of_slit_branch (c := -1)
    (neg_ne_zero.mpr one_ne_zero) hwl.le hδpos (by linarith)
    (fun t ht htw ↦ slit_branch_vertical_right hre ht.2 (fdBoundary_ne_right hre
      (by linarith) him_lo himH fun h ↦ htw (by rw [h]; exact ⟨by linarith, by linarith⟩)))
    hfl hfr hnear
  refine ⟨hint, ?_⟩
  rw [hval, hL, hR, show (ε : ℂ) * Complex.I * -1 = ((-ε : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    show ((-ε : ℝ) : ℂ) * Complex.I * -1 = (ε : ℂ) * Complex.I by push_cast; ring]
  exact log_neg_eps_I_sub_log_eps_I hε

/-- The norm of the shifted contour along the left vertical, in linear form. -/
private lemma norm_fdBoundary_sub_of_mem_Icc_three_four (hre : w.re = -(1 / 2))
    (hs : s ∈ Icc (3 : ℝ) 4) : ‖fdBoundary H s - w‖ =
      |Real.sqrt 3 / 2 + (s - 3) * (H - Real.sqrt 3 / 2) - w.im| := by
  rw [fdBoundary_sub_of_mem_Icc_three_four hre hs, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- **The window of a left-vertical crossing**: the chord-matched window around the
crossing parameter sits inside the open segment range, and its endpoints are exactly
`w ∓ ε·i`. -/
private lemma left_window_endpoints (hre : w.re = -(1 / 2)) (hε : 0 < ε)
    (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    ε / (H - Real.sqrt 3 / 2) < (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) ∧
    (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2) < 1 ∧
    fdBoundary H (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) -
        ε / (H - Real.sqrt 3 / 2)) - w = ((-ε : ℝ) : ℂ) * Complex.I ∧
    fdBoundary H (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) +
        ε / (H - Real.sqrt 3 / 2)) - w = (ε : ℂ) * Complex.I := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hδpos : 0 < ε / (H - Real.sqrt 3 / 2) := div_pos hε hk
  have ht₀k : (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) =
      w.im - Real.sqrt 3 / 2 := div_mul_cancel₀ _ hk.ne'
  have hδk : ε / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ _ hk.ne'
  have hwl : ε / (H - Real.sqrt 3 / 2) < (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) :=
    by rw [div_lt_div_iff_of_pos_right hk]; linarith
  have hwr : (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2)
      < 1 := by rw [← add_div, div_lt_one hk]; linarith
  refine ⟨hwl, hwr, ?_, ?_⟩ <;>
    rw [fdBoundary_sub_of_mem_Icc_three_four hre ⟨by linarith, by linarith⟩]
  · refine congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) ?_
    rw [show ∀ a b : ℝ, 3 + a - b - 3 = a - b by intros; ring, sub_mul]
    linarith
  · refine congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) ?_
    rw [show ∀ a b : ℝ, 3 + a + b - 3 = a + b by intros; ring, add_mul]
    linarith

/-- **The near bound of a left-vertical crossing**: within the chord-matched window the
contour stays within `ε` of `w`. -/
private lemma left_window_near (hre : w.re = -(1 / 2)) (hε : 0 < ε) (hεc : ε < H - w.im)
    (hεv : ε < w.im - Real.sqrt 3 / 2) :
    ∀ s ∈ Icc (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) -
        ε / (H - Real.sqrt 3 / 2))
      (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2)),
      ‖fdBoundary H s - w‖ ≤ ε := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  obtain ⟨hwl, hwr, -, -⟩ := left_window_endpoints hre hε hεc hεv
  set u := (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)
  set δ := ε / (H - Real.sqrt 3 / 2)
  have hδpos : 0 < δ := div_pos hε hk
  have ht₀k : u * (H - Real.sqrt 3 / 2) = w.im - Real.sqrt 3 / 2 := div_mul_cancel₀ _ hk.ne'
  have hδk : δ * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ _ hk.ne'
  intro s hs
  have hl := mul_le_mul_of_nonneg_right (show u - δ ≤ s - 3 by linarith [hs.1]) hk.le
  have hr := mul_le_mul_of_nonneg_right (show s - 3 ≤ u + δ by linarith [hs.2]) hk.le
  rw [sub_mul u δ, ht₀k, hδk] at hl
  rw [add_mul u δ, ht₀k, hδk] at hr
  rw [norm_fdBoundary_sub_of_mem_Icc_three_four hre
    ⟨by linarith [hs.1, hwl], by linarith [hs.2, hwr]⟩]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The far bounds of a left-vertical crossing**: beyond the chord-matched window the
contour keeps distance more than `ε` from `w`. -/
private lemma left_window_bounds (hre : w.re = -(1 / 2)) (hε : 0 < ε) (hε₁ : ε < 1)
    (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    (∀ s ∈ Ioo (0 : ℝ) (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) -
      ε / (H - Real.sqrt 3 / 2)), ε < ‖fdBoundary H s - w‖) ∧
    ∀ s ∈ Ioo (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) +
      ε / (H - Real.sqrt 3 / 2)) (5 : ℝ), ε < ‖fdBoundary H s - w‖ := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  obtain ⟨hwl, hwr, -, -⟩ := left_window_endpoints hre hε hεc hεv
  set u := (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)
  set δ := ε / (H - Real.sqrt 3 / 2)
  have hδpos : 0 < δ := div_pos hε hk
  have ht₀k : u * (H - Real.sqrt 3 / 2) = w.im - Real.sqrt 3 / 2 := div_mul_cancel₀ _ hk.ne'
  have hδk : δ * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ _ hk.ne'
  refine ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · rcases le_or_gt s 3 with h3 | h3
    · exact lt_norm_sub_left_of_off_segment hre hε₁ hεa hεc
        ⟨hs.1.le, by linarith [hs.2, hwr]⟩ (Or.inl h3)
    · have hlt := mul_lt_mul_of_pos_right (show s - 3 < u - δ by linarith [hs.2]) hk
      rw [sub_mul u δ, ht₀k, hδk] at hlt
      rw [norm_fdBoundary_sub_of_mem_Icc_three_four hre ⟨h3.le, by linarith [hs.2, hwr]⟩]
      exact lt_of_lt_of_le
        (show ε < -(Real.sqrt 3 / 2 + (s - 3) * (H - Real.sqrt 3 / 2) - w.im) by linarith)
        (neg_le_abs _)
  · rcases le_or_gt s 4 with h4 | h4
    · have hlt := mul_lt_mul_of_pos_right (show u + δ < s - 3 by linarith [hs.1]) hk
      rw [add_mul u δ, ht₀k, hδk] at hlt
      rw [norm_fdBoundary_sub_of_mem_Icc_three_four hre ⟨by linarith [hs.1], h4⟩]
      exact lt_of_lt_of_le
        (show ε < Real.sqrt 3 / 2 + (s - 3) * (H - Real.sqrt 3 / 2) - w.im by linarith)
        (le_abs_self _)
    · exact lt_norm_sub_left_of_off_segment hre hε₁ hεa hεc
        ⟨by linarith [hs.1], hs.2.le⟩ (Or.inr h4.le)

/-- **The excision collapse at a left-vertical point**: for small `ε`, the `ε`-excised index
integrand of the boundary contour about `w` is interval integrable, and its integral is
exactly `-πi`. -/
private lemma truncated_integral_spec_left (hre : w.re = -(1 / 2))
    (him_lo : Real.sqrt 3 / 2 < w.im) (himH : w.im < H) (hε : 0 < ε) (hε₁ : ε < 1)
    (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
      -(Real.pi : ℂ) * Complex.I := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hδpos : 0 < ε / (H - Real.sqrt 3 / 2) := div_pos hε hk
  obtain ⟨hwl, hwr, hL, hR⟩ := left_window_endpoints hre hε hεc hεv
  obtain ⟨hfl, hfr⟩ := left_window_bounds hre hε hε₁ hεa hεc hεv
  have hnear := left_window_near hre hε hεc hεv
  obtain ⟨hint, hval⟩ := truncated_integral_spec_of_slit_branch (c := 1) one_ne_zero
    (t₀ := 3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)) (by linarith) hδpos
    (by linarith)
    (fun t ht htw ↦ by
      rw [mul_one]
      refine slit_branch_vertical_left hre ht.2 (fdBoundary_ne_left hre (by linarith)
        him_lo himH fun h ↦ htw ?_)
      rw [h]
      exact ⟨by linarith, by linarith⟩)
    hfl hfr hnear
  refine ⟨hint, ?_⟩
  rw [hval, hL, hR, mul_one, mul_one]
  exact log_neg_eps_I_sub_log_eps_I hε

/-- A point of an open vertical edge lies strictly above the corner row. -/
private lemma sqrt_three_div_two_lt_im (hre : w.re = 1 / 2 ∨ w.re = -(1 / 2))
    (hnorm : 1 < ‖w‖) (him : 0 < w.im) : Real.sqrt 3 / 2 < w.im := by
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hre2 : w.re ^ 2 = 1 / 4 := by rcases hre with h | h <;> rw [h] <;> norm_num
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 3, norm_nonneg w]

/-- **The principal value at a vertical-edge point**: the Cauchy principal value of the
index integrand of the boundary contour about a point of an open vertical edge is `-πi` —
half a clockwise turn, as the contour passes straight through `w` along the edge. -/
theorem hasCauchyPVAt_fdBoundary_vertical (hre : w.re = 1 / 2 ∨ w.re = -(1 / 2))
    (hnorm : 1 < ‖w‖) (him : 0 < w.im) (himH : w.im < H) :
    Contour.HasCauchyPVAt (fdBoundary H) 0 5 (fun z ↦ (z - w)⁻¹) w
      (-(Real.pi : ℂ) * Complex.I) := by
  have him_lo := sqrt_three_div_two_lt_im hre hnorm him
  have hb : (0 : ℝ) <
      min (min 1 (‖w‖ - 1)) (min (H - w.im) (w.im - Real.sqrt 3 / 2)) :=
    lt_min (lt_min one_pos (by linarith)) (lt_min (by linarith) (by linarith))
  have hIoo : Ioo (0 : ℝ) (min (min 1 (‖w‖ - 1)) (min (H - w.im) (w.im - Real.sqrt 3 / 2)))
      ∈ 𝓝[>] (0 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hb))
  have hspec : ∀ ε ∈ Ioo (0 : ℝ)
      (min (min 1 (‖w‖ - 1)) (min (H - w.im) (w.im - Real.sqrt 3 / 2))),
      IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
          then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
      ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
          then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
        -(Real.pi : ℂ) * Complex.I := by
    intro ε hε
    have h1 := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have ha := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hc := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hv := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rcases hre with h | h
    · exact truncated_integral_spec_right h him_lo himH hε.1 h1 ha hc hv
    · exact truncated_integral_spec_left h him_lo himH hε.1 h1 ha hc hv
  refine Contour.hasCauchyPVAt_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [hIoo] with ε hε
    exact (hspec ε hε).1
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hIoo] with ε hε
    exact ((hspec ε hε).2).symm

/-- **The winding number of the boundary contour at a vertical-edge point is `-1/2`**: the
point sits on an open vertical edge, and the principal-value normalization sees exactly half
a clockwise turn. -/
theorem windingNumber_fdBoundary_vertical (hre : w.re = 1 / 2 ∨ w.re = -(1 / 2))
    (hnorm : 1 < ‖w‖) (him : 0 < w.im) (himH : w.im < H) :
    Contour.windingNumber (fdBoundary H) 0 5 w = -(1 / 2 : ℂ) := by
  rw [Contour.windingNumber_eq_of_hasCauchyPVAt
    (hasCauchyPVAt_fdBoundary_vertical hre hnorm him himH)]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-! ## The arc

A point `w` of the open unit arc is `fdBoundary H t₀` for a unique `t₀ ∈ (1, 3)`; the arc is
one smooth circle parameterization through `t = 2`, so no corner is in the way even at `i`.
The adapted branch is `c = w⁻¹`, whose cut ray `{r·w : r ≤ 1}` runs from `w` through the
open unit disc and leaves through the lower half-plane, missing the rest of the contour. The
chord geometry is the one proven at `i`, with `t₀` in place of `2`.
-/

/-- The argument of a point of the open unit arc lies in the open middle third of
`(0, π)`. -/
private lemma arg_mem_Ioo (hnorm : ‖w‖ = 1) (hre : |w.re| < 1 / 2) (him : 0 < w.im) :
    Complex.arg w ∈ Ioo (Real.pi / 3) (2 * Real.pi / 3) := by
  have hw0 : w ≠ 0 := fun h ↦ by rw [h, norm_zero] at hnorm; norm_num at hnorm
  have hcos : Real.cos (Complex.arg w) = w.re := by rw [Complex.cos_arg hw0, hnorm, div_one]
  have habs := abs_lt.mp hre
  have harg_lt : Complex.arg w < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr him.ne')
  have harg_pos : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.mpr him.le
  constructor
  · by_contra hle
    push Not at hle
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi harg_pos (by linarith [Real.pi_pos]) hle
    rw [hcos, Real.cos_pi_div_three] at hmono
    linarith [habs.2]
  · by_contra hle
    push Not at hle
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) harg_lt.le hle
    rw [hcos, show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hmono
    linarith [habs.1]

/-- Every point of the open unit arc is hit by the arc parameterization. -/
private lemma exists_arc_param (hnorm : ‖w‖ = 1) (hre : |w.re| < 1 / 2) (him : 0 < w.im) :
    ∃ t₀ ∈ Ioo (1 : ℝ) 3, fdBoundary H t₀ = w := by
  have hπ := Real.pi_pos
  have h13 := arg_mem_Ioo hnorm hre him
  have h1 : (1 : ℝ) < 6 * Complex.arg w / Real.pi - 1 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hπ]
    nlinarith [h13.1]
  have h3 : 6 * Complex.arg w / Real.pi - 1 < 3 := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hπ]
    nlinarith [h13.2]
  refine ⟨6 * Complex.arg w / Real.pi - 1, ⟨h1, h3⟩, ?_⟩
  have hcurve : fdBoundary H (6 * Complex.arg w / Real.pi - 1) =
      circleMap 0 1 ((6 * Complex.arg w / Real.pi - 1 + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ⟨h1.le, h3.le⟩
  have hpolar := Complex.norm_mul_exp_arg_mul_I w
  rw [hnorm, Complex.ofReal_one, one_mul] at hpolar
  rw [hcurve,
    show (6 * Complex.arg w / Real.pi - 1 + 1) * (Real.pi / 6) = Complex.arg w by
      field_simp; ring,
    show circleMap 0 1 (Complex.arg w) =
      Complex.exp ((Complex.arg w : ℂ) * Complex.I) by simp [circleMap]]
  exact hpolar

/-- On the arc the distance between two contour points is the chord distance
`2·sin(|t - t₀|·π/12)`, up to the absolute value inside the sine. -/
private lemma norm_fdBoundary_sub_fdBoundary_arc (ht : t ∈ Icc (1 : ℝ) 3)
    (ht₀ : t₀ ∈ Icc (1 : ℝ) 3) :
    ‖fdBoundary H t - fdBoundary H t₀‖ = 2 * |Real.sin ((t - t₀) * (Real.pi / 12))| := by
  rw [eqOn_fdBoundary_arc H ht, eqOn_fdBoundary_arc H ht₀, ← Complex.dist_eq,
    dist_circleMap_eq_two_mul_abs_sin,
    show ((t + 1) * (Real.pi / 6) - (t₀ + 1) * (Real.pi / 6)) / 2 = (t - t₀) * (Real.pi / 12)
      by ring]
  norm_num

/-- Far from the crossing along the arc, the chord distance strictly exceeds the excision
chord. -/
private lemma lt_norm_sub_arc_of_far (ht : t ∈ Icc (1 : ℝ) 3) (ht₀ : t₀ ∈ Icc (1 : ℝ) 3)
    (hδ : 0 < δ) (hfar : δ < |t - t₀|) :
    2 * Real.sin (δ * (Real.pi / 12)) < ‖fdBoundary H t - fdBoundary H t₀‖ := by
  have habs2 : |t - t₀| ≤ 2 := by
    rw [abs_le]
    exact ⟨by linarith [ht.1, ht₀.2], by linarith [ht.2, ht₀.1]⟩
  rw [norm_fdBoundary_sub_fdBoundary_arc ht ht₀,
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
      nlinarith [Real.pi_pos]),
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
  have hmono : Real.sin (δ * (Real.pi / 12)) < Real.sin (|t - t₀| * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos, abs_nonneg (t - t₀)], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_lt_mul_of_pos_right hfar (by positivity)
  linarith

/-- Near the crossing along the arc, the chord distance is at most the excision chord. -/
private lemma norm_sub_arc_le_of_near (ht : t ∈ Icc (1 : ℝ) 3) (ht₀ : t₀ ∈ Icc (1 : ℝ) 3)
    (hδ2 : δ ≤ 2) (hnear : |t - t₀| ≤ δ) :
    ‖fdBoundary H t - fdBoundary H t₀‖ ≤ 2 * Real.sin (δ * (Real.pi / 12)) := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hnear
  rw [norm_fdBoundary_sub_fdBoundary_arc ht ht₀,
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
      nlinarith [Real.pi_pos, abs_nonneg (t - t₀)]),
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
  have hmono : Real.sin (|t - t₀| * (Real.pi / 12)) ≤ Real.sin (δ * (Real.pi / 12)) := by
    refine Real.sin_le_sin_of_le_of_le_pi_div_two
      (by nlinarith [Real.pi_pos, abs_nonneg (t - t₀)]) (by nlinarith [Real.pi_pos]) ?_
    exact mul_le_mul_of_nonneg_right hnear (by positivity)
  linarith

/-- The rotated shifted contour along the arc, with signed offset: the half-angle sine
turned a quarter past the offset half-angle. The rotation `w⁻¹` makes the polar data
independent of the crossing point. -/
private lemma fdBoundary_sub_mul_inv_polar {ξ : ℝ} (ht₀ : t₀ ∈ Icc (1 : ℝ) 3)
    (hξ : t₀ + ξ ∈ Icc (1 : ℝ) 3) :
    (fdBoundary H (t₀ + ξ) - fdBoundary H t₀) * (fdBoundary H t₀)⁻¹ =
      2 * ((Real.sin (ξ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I *
        Complex.exp (((ξ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I) := by
  have h1 : fdBoundary H (t₀ + ξ) =
      Complex.exp ((((t₀ + ξ + 1) * (Real.pi / 6) : ℝ) : ℂ) * Complex.I) := by
    rw [show Complex.exp ((((t₀ + ξ + 1) * (Real.pi / 6) : ℝ) : ℂ) * Complex.I) =
      circleMap 0 1 ((t₀ + ξ + 1) * (Real.pi / 6)) by simp [circleMap]]
    exact eqOn_fdBoundary_arc H hξ
  have h2 : fdBoundary H t₀ =
      Complex.exp ((((t₀ + 1) * (Real.pi / 6) : ℝ) : ℂ) * Complex.I) := by
    rw [show Complex.exp ((((t₀ + 1) * (Real.pi / 6) : ℝ) : ℂ) * Complex.I) =
      circleMap 0 1 ((t₀ + 1) * (Real.pi / 6)) by simp [circleMap]]
    exact eqOn_fdBoundary_arc H ht₀
  rw [h1, h2, exp_mul_I_sub_exp_mul_I,
    show ((t₀ + ξ + 1) * (Real.pi / 6) - (t₀ + 1) * (Real.pi / 6)) / 2 = ξ * (Real.pi / 12)
      by ring,
    ← Complex.exp_neg, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The rotated shifted contour beside the crossing, right side, in polar form: radial part
`2·sin(δ·π/12)` and argument `π/2 + δ·π/12`. -/
private lemma fdBoundary_sub_mul_inv_add_eq (ht₀ : t₀ ∈ Icc (1 : ℝ) 3) (hδ : 0 < δ)
    (hδ3 : t₀ + δ ≤ 3) :
    (fdBoundary H (t₀ + δ) - fdBoundary H t₀) * (fdBoundary H t₀)⁻¹ =
      ((2 * Real.sin (δ * (Real.pi / 12)) : ℝ) : ℂ) *
        Complex.exp (((Real.pi / 2 + δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I) := by
  rw [fdBoundary_sub_mul_inv_polar ht₀ ⟨by linarith [ht₀.1], hδ3⟩,
    show ((Real.pi / 2 + δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I =
      (Real.pi : ℂ) / 2 * Complex.I + ((δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
    Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  push_cast
  ring

/-- The rotated shifted contour beside the crossing, left side, in polar form: the mirror
argument `-(π/2 + δ·π/12)`. -/
private lemma fdBoundary_sub_mul_inv_sub_eq (ht₀ : t₀ ∈ Icc (1 : ℝ) 3) (hδ : 0 < δ)
    (hδ1 : 1 ≤ t₀ - δ) :
    (fdBoundary H (t₀ - δ) - fdBoundary H t₀) * (fdBoundary H t₀)⁻¹ =
      ((2 * Real.sin (δ * (Real.pi / 12)) : ℝ) : ℂ) *
        Complex.exp (((-(Real.pi / 2 + δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I) := by
  have h := fdBoundary_sub_mul_inv_polar (H := H) (ξ := -δ) ht₀
    ⟨by linarith, by linarith [ht₀.2]⟩
  rw [show t₀ + -δ = t₀ - δ by ring, show -δ * (Real.pi / 12) = -(δ * (Real.pi / 12)) by ring,
    Real.sin_neg] at h
  rw [h, show ((-(Real.pi / 2 + δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I =
      -((Real.pi : ℂ) / 2 * Complex.I) + ((-(δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
    Complex.exp_add, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  push_cast
  ring

/-- **The symmetric log difference at the crossing**: the two endpoint logarithms of the
`δ`-excised arc for the rotated branch differ by the pure phase `-(π + δ·π/6)·i` — the chord
norms agree, and only the argument difference survives. -/
private lemma log_sub_log_arc (ht₀ : t₀ ∈ Icc (1 : ℝ) 3) (hδ : 0 < δ) (hδ1 : 1 ≤ t₀ - δ)
    (hδ3 : t₀ + δ ≤ 3) :
    Complex.log ((fdBoundary H (t₀ - δ) - fdBoundary H t₀) * (fdBoundary H t₀)⁻¹) -
      Complex.log ((fdBoundary H (t₀ + δ) - fdBoundary H t₀) * (fdBoundary H t₀)⁻¹) =
      -((Real.pi + δ * (Real.pi / 6) : ℝ) : ℂ) * Complex.I := by
  have hπ := Real.pi_pos
  have hδ2 : δ ≤ 2 := by linarith [ht₀.1, ht₀.2]
  have hsin : 0 < Real.sin (δ * (Real.pi / 12)) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  rw [fdBoundary_sub_mul_inv_sub_eq ht₀ hδ hδ1, fdBoundary_sub_mul_inv_add_eq ht₀ hδ hδ3,
    Complex.log_ofReal_mul (by linarith) (Complex.exp_ne_zero _),
    Complex.log_ofReal_mul (by linarith) (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; nlinarith) (by simp; nlinarith),
    Complex.log_exp (by simp; nlinarith) (by simp; nlinarith)]
  push_cast
  ring

/-- The contour meets an arc point only at its arc parameter. -/
private lemma fdBoundary_ne_arc (hH : 1 < H) (hre : |w.re| < 1 / 2)
    (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3) (hw : fdBoundary H t₀ = w)
    (hts : t ≠ t₀) : fdBoundary H t ≠ w := by
  intro heq
  rcases le_or_gt t 1 with h1 | h1
  · have hr := re_fdBoundary_of_le_one (H := H) h1
    rw [heq] at hr
    rw [hr] at hre
    norm_num at hre
  · rcases le_or_gt t 3 with h3 | h3
    · exact hts (injOn_fdBoundary_arc H ⟨h1.le, h3⟩ ⟨ht₀.1.le, ht₀.2.le⟩
        (heq.trans hw.symm))
    · rcases le_or_gt t 4 with h4 | h4
      · have hr := re_fdBoundary_of_le_four (H := H) h3 h4
        rw [heq] at hr
        rw [hr] at hre
        norm_num at hre
      · have hi := im_fdBoundary_of_gt_four (H := H) h4
        rw [heq] at hi
        have him1 : w.im ≤ 1 := by
          rw [← hw]
          exact im_fdBoundary_arc_le H ⟨ht₀.1.le, ht₀.2.le⟩
        linarith

/-- For an arc point, the branch rotated by `w⁻¹` is slit-plane-valued wherever the contour
misses `w`: the cut ray `{r·w : r ≤ 1}` meets the contour only at `w` itself. -/
private lemma slit_branch_arc (hH : 1 < H) (hnorm : ‖w‖ = 1) (him : 0 < w.im)
    (ht : t ∈ Icc (0 : ℝ) 5) (hne : fdBoundary H t ≠ w) :
    (fdBoundary H t - w) * w⁻¹ ∈ Complex.slitPlane := by
  have hw0 : w ≠ 0 := fun h ↦ by rw [h, norm_zero] at hnorm; norm_num at hnorm
  by_contra hmem
  rw [Complex.mem_slitPlane_iff] at hmem
  push Not at hmem
  obtain ⟨hre0, him0⟩ := hmem
  set x := ((fdBoundary H t - w) * w⁻¹).re with hx
  have hxeq : (fdBoundary H t - w) * w⁻¹ = (x : ℂ) := Complex.ext rfl (by simpa using him0)
  have hγ : fdBoundary H t = (1 + (x : ℂ)) * w := by
    have h1 := congrArg (· * w) hxeq
    simp only [inv_mul_cancel_right₀ hw0] at h1
    linear_combination h1
  rcases le_or_gt 0 (1 + x) with hpos | hneg
  · have hn := congrArg norm hγ
    rw [norm_mul, hnorm, mul_one, show (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] at hn
    have h1 := one_le_norm_fdBoundary hH.le ht
    have hx0 : x = 0 := le_antisymm hre0 (by rw [hn] at h1; linarith)
    refine hne ?_
    rw [hγ, hx0]
    push_cast
    ring
  · have hi := congrArg Complex.im hγ
    rw [show (1 + (x : ℂ)) * w = ((1 + x : ℝ) : ℂ) * w by push_cast; ring] at hi
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero] at hi
    have him2 := sqrt_three_div_two_le_im_fdBoundary
      (le_of_lt (sqrt_three_div_two_lt_one.trans hH)) ht
    nlinarith [Real.sqrt_nonneg 3, mul_neg_of_neg_of_pos hneg him]

/-- **The chord-matched half-width fits the window**: for an excision radius `ε` below both
corner chords, the half-width `δ(ε)` is positive, keeps the window inside the open arc
range, and reproduces `ε` as its own chord. -/
private lemma arcExcisionHalfWidth_spec (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3) (hε : 0 < ε)
    (hεl : ε < 2 * Real.sin ((t₀ - 1) * (Real.pi / 12)))
    (hεr : ε < 2 * Real.sin ((3 - t₀) * (Real.pi / 12))) :
    0 < fdBoundaryArcExcisionHalfWidth ε ∧
      fdBoundaryArcExcisionHalfWidth ε < t₀ - 1 ∧
      fdBoundaryArcExcisionHalfWidth ε < 3 - t₀ ∧
      2 * Real.sin (fdBoundaryArcExcisionHalfWidth ε * (Real.pi / 12)) = ε := by
  have hπ := Real.pi_pos
  have key : ∀ m : ℝ, 0 < m → m ≤ 2 → ε < 2 * Real.sin (m * (Real.pi / 12)) →
      fdBoundaryArcExcisionHalfWidth ε < m := by
    intro m hm hm2 hεm
    have harc : Real.arcsin (ε / 2) < m * (Real.pi / 12) := by
      have h1 : Real.arcsin (ε / 2) < Real.arcsin (Real.sin (m * (Real.pi / 12))) :=
        Real.arcsin_lt_arcsin (by linarith) (by linarith) (Real.sin_le_one _)
      rwa [Real.arcsin_sin (by nlinarith) (by nlinarith)] at h1
    rw [fdBoundaryArcExcisionHalfWidth_def, div_mul_eq_mul_div, div_lt_iff₀ hπ]
    nlinarith
  have hεπ : ε < 2 * Real.sin (Real.pi / 12) := by
    rcases le_total (t₀ - 1) (3 - t₀) with h | h
    · refine hεl.trans_le (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      refine Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [ht₀.1]) (by nlinarith) ?_
      nlinarith [ht₀.1]
    · refine hεr.trans_le (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      refine Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [ht₀.2]) (by nlinarith) ?_
      nlinarith [ht₀.2]
  obtain ⟨hδ0, _, h2sin⟩ :=
    fdBoundaryArcExcisionHalfWidth_pos_and_lt_one_and_two_mul_sin_eq hε hεπ
  exact ⟨hδ0, key _ (by linarith [ht₀.1]) (by linarith [ht₀.2]) hεl,
    key _ (by linarith [ht₀.2]) (by linarith [ht₀.1]) hεr, h2sin⟩

/-- Left of the excised window, the contour keeps distance more than `ε` from the arc
point. -/
private lemma lt_norm_sub_arc_of_far_left (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3)
    (hw : fdBoundary H t₀ = w) (hδ : 0 < δ)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε) (hε₁ : ε < 1 / 2 - w.re)
    (hs : s ∈ Ioo (0 : ℝ) (t₀ - δ)) : ε < ‖fdBoundary H s - w‖ := by
  rcases le_or_gt s 1 with h1 | h1
  · have hr : (fdBoundary H s - w).re = 1 / 2 - w.re := by
      rw [Complex.sub_re, re_fdBoundary_of_le_one h1]
    calc ε < 1 / 2 - w.re := hε₁
      _ ≤ |(fdBoundary H s - w).re| := by rw [hr]; exact le_abs_self _
      _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_re_le_norm _
  · rw [← hw, ← h2sin]
    refine lt_norm_sub_arc_of_far ⟨h1.le, by linarith [hs.2, ht₀.2]⟩ ⟨ht₀.1.le, ht₀.2.le⟩
      hδ ?_
    rw [abs_sub_comm, abs_of_pos (by linarith [hs.2] : (0 : ℝ) < t₀ - s)]
    linarith [hs.2]

/-- Right of the excised window, the contour keeps distance more than `ε` from the arc
point. -/
private lemma lt_norm_sub_arc_of_far_right (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3)
    (hw : fdBoundary H t₀ = w) (hδ : 0 < δ)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε)
    (hε₂ : ε < w.re + 1 / 2) (hεc : ε < H - 1) (hs : s ∈ Ioo (t₀ + δ) (5 : ℝ)) :
    ε < ‖fdBoundary H s - w‖ := by
  have him1 : w.im ≤ 1 := by
    rw [← hw]
    exact im_fdBoundary_arc_le H ⟨ht₀.1.le, ht₀.2.le⟩
  rcases le_or_gt s 3 with h3 | h3
  · rw [← hw, ← h2sin]
    refine lt_norm_sub_arc_of_far ⟨by linarith [hs.1, ht₀.1], h3⟩ ⟨ht₀.1.le, ht₀.2.le⟩
      hδ ?_
    rw [abs_of_pos (by linarith [hs.1] : (0 : ℝ) < s - t₀)]
    linarith [hs.1]
  · rcases le_or_gt s 4 with h4 | h4
    · have hr : (fdBoundary H s - w).re = -(1 / 2) - w.re := by
        rw [Complex.sub_re, re_fdBoundarySegment4 H ⟨h3.le, h4⟩]
      calc ε < w.re + 1 / 2 := hε₂
        _ ≤ |(fdBoundary H s - w).re| := by
          rw [hr, abs_sub_comm, show w.re - -(1 / 2) = w.re + 1 / 2 by ring]
          exact le_abs_self _
        _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_re_le_norm _
    · have hi : (fdBoundary H s - w).im = H - w.im := by
        rw [Complex.sub_im, im_fdBoundarySegment5 H ⟨h4.le, hs.2.le⟩]
      calc ε < H - w.im := by linarith
        _ ≤ |(fdBoundary H s - w).im| := by rw [hi]; exact le_abs_self _
        _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_im_le_norm _

/-- **The excision collapse at an arc point**: for small `ε`, the `ε`-excised index
integrand of the boundary contour about `w` is interval integrable, and its integral is
exactly `-πi - 2·arcsin(ε/2)·i` — the value of the telescope at the matched half-width. -/
private lemma truncated_integral_spec_arc (hH : 1 < H) (hnorm : ‖w‖ = 1)
    (hre : |w.re| < 1 / 2) (him : 0 < w.im) (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3)
    (hw : fdBoundary H t₀ = w) (hε : 0 < ε)
    (hεl : ε < 2 * Real.sin ((t₀ - 1) * (Real.pi / 12)))
    (hεr : ε < 2 * Real.sin ((3 - t₀) * (Real.pi / 12)))
    (hε₁ : ε < 1 / 2 - w.re) (hε₂ : ε < w.re + 1 / 2) (hεc : ε < H - 1) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
      -(Real.pi : ℂ) * Complex.I - ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
  obtain ⟨hδ0, hδl, hδr, h2sin⟩ := arcExcisionHalfWidth_spec ht₀ hε hεl hεr
  set δ := fdBoundaryArcExcisionHalfWidth ε with hδ_def
  have hw0 : w ≠ 0 := fun h ↦ by rw [h, norm_zero] at hnorm; norm_num at hnorm
  obtain ⟨hint, hval⟩ := truncated_integral_spec_of_slit_branch (c := w⁻¹)
    (inv_ne_zero hw0) (by linarith [ht₀.1]) hδ0 (by linarith [ht₀.2])
    (fun t ht htw ↦ slit_branch_arc hH hnorm him ht (fdBoundary_ne_arc hH hre ht₀ hw
      fun h ↦ htw (by rw [h]; exact ⟨by linarith, by linarith⟩)))
    (fun s hs ↦ lt_norm_sub_arc_of_far_left ht₀ hw hδ0 h2sin hε₁ hs)
    (fun s hs ↦ lt_norm_sub_arc_of_far_right ht₀ hw hδ0 h2sin hε₂ hεc hs)
    (fun s hs ↦ by
      rw [← hw, ← h2sin]
      exact norm_sub_arc_le_of_near ⟨by linarith [hs.1, ht₀.1], by linarith [hs.2, ht₀.2]⟩
        ⟨ht₀.1.le, ht₀.2.le⟩ (by linarith [ht₀.1, ht₀.2])
        (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩))
  refine ⟨hint, ?_⟩
  rw [hval, ← hw, log_sub_log_arc ⟨ht₀.1.le, ht₀.2.le⟩ hδ0 (by linarith [ht₀.1])
    (by linarith [ht₀.2]),
    show δ * (Real.pi / 6) = 2 * Real.arcsin (ε / 2) by
      rw [hδ_def, fdBoundaryArcExcisionHalfWidth_def]; field_simp; ring]
  push_cast
  ring

/-- The excised arc values converge to `-πi` as the excision radius shrinks. -/
private lemma tendsto_neg_pi_sub_arcsin :
    Tendsto (fun ε : ℝ ↦ -(Real.pi : ℂ) * Complex.I -
        ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝 (-(Real.pi : ℂ) * Complex.I)) := by
  have hc : Continuous fun ε : ℝ ↦ -(Real.pi : ℂ) * Complex.I -
      ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
    refine continuous_const.sub ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
    exact continuous_const.mul (Real.continuous_arcsin.comp (continuous_id.div_const 2))
  simpa [Real.arcsin_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The five distance clearances of an arc point are simultaneously positive. -/
private lemma arc_min_radius_pos (hH : 1 < H) (hre : |w.re| < 1 / 2)
    (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3) :
    0 < min (min (2 * Real.sin ((t₀ - 1) * (Real.pi / 12)))
        (2 * Real.sin ((3 - t₀) * (Real.pi / 12))))
      (min (1 / 2 - w.re) (min (w.re + 1 / 2) (H - 1))) := by
  have hπ := Real.pi_pos
  have habs := abs_lt.mp hre
  refine lt_min (lt_min ?_ ?_)
    (lt_min (by linarith [habs.2]) (lt_min (by linarith [habs.1]) (by linarith)))
  · exact mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [ht₀.1]) (by nlinarith [ht₀.1, ht₀.2]))
  · exact mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [ht₀.2]) (by nlinarith [ht₀.1, ht₀.2]))

/-- **The principal value at an arc point**: the Cauchy principal value of the index
integrand of the boundary contour about a point of the open unit arc is `-πi` — half a
clockwise turn, as the contour passes smoothly through `w` along the arc. -/
theorem hasCauchyPVAt_fdBoundary_arc (hH : 1 < H) (hnorm : ‖w‖ = 1)
    (hre : |w.re| < 1 / 2) (him : 0 < w.im) :
    Contour.HasCauchyPVAt (fdBoundary H) 0 5 (fun z ↦ (z - w)⁻¹) w
      (-(Real.pi : ℂ) * Complex.I) := by
  obtain ⟨t₀, ht₀, hw⟩ := exists_arc_param (H := H) hnorm hre him
  set b := min (min (2 * Real.sin ((t₀ - 1) * (Real.pi / 12)))
      (2 * Real.sin ((3 - t₀) * (Real.pi / 12))))
    (min (1 / 2 - w.re) (min (w.re + 1 / 2) (H - 1))) with hb_def
  have hb : 0 < b := arc_min_radius_pos hH hre ht₀
  have hIoo : Ioo (0 : ℝ) b ∈ 𝓝[>] (0 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hb))
  have hspec : ∀ ε ∈ Ioo (0 : ℝ) b,
      IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
          then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
      ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
          then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
        -(Real.pi : ℂ) * Complex.I - ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I :=
    fun ε hε ↦ truncated_integral_spec_arc hH hnorm hre him ht₀ hw hε.1
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      (hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      (hε.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))
      (hε.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _))))
  refine Contour.hasCauchyPVAt_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [hIoo] with ε hε
    exact (hspec ε hε).1
  · refine Tendsto.congr' ?_ tendsto_neg_pi_sub_arcsin
    filter_upwards [hIoo] with ε hε
    exact ((hspec ε hε).2).symm

/-- **The winding number of the boundary contour at an arc point is `-1/2`**: the point sits
on the open unit arc, and the principal-value normalization sees exactly half a clockwise
turn. -/
theorem windingNumber_fdBoundary_arc (hH : 1 < H) (hnorm : ‖w‖ = 1)
    (hre : |w.re| < 1 / 2) (him : 0 < w.im) :
    Contour.windingNumber (fdBoundary H) 0 5 w = -(1 / 2 : ℂ) := by
  rw [Contour.windingNumber_eq_of_hasCauchyPVAt
    (hasCauchyPVAt_fdBoundary_arc hH hnorm hre him)]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end ModularForm

end TauCeti

end
