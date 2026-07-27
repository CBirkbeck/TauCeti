/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.SpecialFunctions.JordanIntegral
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Jordan's lemma

A large semicircular arc contributes little to a contour integral whose integrand carries an
oscillatory factor `e^{iaz}` with `a > 0`:

$$\left\|\int_{C_R} f(z)\,e^{iaz}\,dz\right\| \;\le\; \frac{\pi}{a}\,M_R,
\qquad M_R = \sup_{C_R} \|f\|,$$

where `C_R` is the upper semicircle of radius `R` traversed counterclockwise.

The point is that the **estimate** needs no decay of `f` beyond boundedness, whereas the naive
`ML` estimate `‖∫‖ ≤ (πR) · M_R` would need `M_R = o(1/R)` even to stay bounded. Concluding that
the arc contribution actually **vanishes** is a further step, and does require `M_R → 0` — that
is the hypothesis of `tendsto_integral_semicircle_exp_mul_nhds_zero`. The gain comes from
`|e^{iaz}| = e^{-aR\sin θ}` on the arc together with `TauCeti.integral_exp_neg_mul_sin_le`,
whose `1/(aR)` cancels the arc length `πR`.

The estimate is sharp enough for the standard application: `f z = z⁻¹` has `M_R = 1/R → 0`, so
the arc term dies and the half-disc identity of `WorkedExamples/HalfDisc/HalfResidue.lean`
survives the limit `R → ∞`. Note that *without* the oscillatory factor the arc term does not
vanish at all — `∫ dz/z` over the arc is `iπ` for every `R` — so the factor is essential, not a
convenience.

## Main results

* `TauCeti.Contour.norm_integral_semicircle_exp_mul_le` — Jordan's lemma as an explicit bound.
* `TauCeti.Contour.tendsto_integral_semicircle_exp_mul_nhds_zero` — the arc contribution tends
  to `0` along any radius filter on which the sup bound tends to `0`.

## References

* C. Jordan, *Cours d'analyse de l'École Polytechnique*, vol. 2 (1894), §270.
* P. Henrici, *Applied and Computational Complex Analysis*, vol. 1, §4.8.
-/

public section

noncomputable section

open Real Complex MeasureTheory Set Filter Topology

namespace TauCeti.Contour

/-- On the circle of radius `R`, the oscillatory factor has norm `e^{-aR sin θ}`. -/
private theorem norm_exp_mul_circleMap (a R θ : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ) * circleMap 0 R θ)‖ = Real.exp (-(a * R) * Real.sin θ) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [circleMap, zero_add, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
    sub_self, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, sub_zero, mul_im, one_mul, add_zero,
    zero_sub, neg_mul, neg_inj]
  ring

/-- **Jordan's lemma.** If `‖f‖ ≤ M` on the upper semicircle of radius `R > 0`, then for `a > 0`
the arc contribution of `f z · e^{iaz}` is at most `π M / a` in norm — a bound independent of
`R`, obtained without assuming any decay of `f`. -/
theorem norm_integral_semicircle_exp_mul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a R M : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (hM : ∀ θ ∈ Icc (0 : ℝ) π, ‖f (circleMap 0 R θ)‖ ≤ M) :
    ‖∫ θ in (0 : ℝ)..π, (Complex.exp (Complex.I * (a : ℂ) * circleMap 0 R θ) *
        deriv (circleMap 0 R) θ) • f (circleMap 0 R θ)‖ ≤ π * M / a := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, Real.pi_nonneg⟩)
  rcases hR.eq_or_lt with rfl | hR
  · -- Degenerate radius: the arc is a point, `deriv (circleMap 0 0) = 0`, so the integral is `0`.
    have hderiv : ∀ θ : ℝ, deriv (circleMap 0 0) θ = 0 := by simp [circleMap_zero_radius]
    simp only [hderiv, mul_zero, zero_smul, intervalIntegral.integral_zero, norm_zero]
    exact div_nonneg (mul_nonneg Real.pi_nonneg hM0) ha.le
  have hbound : ∀ᵐ θ ∂volume, θ ∈ Ioc (0 : ℝ) π →
      ‖(Complex.exp (Complex.I * (a : ℂ) * circleMap 0 R θ) *
          deriv (circleMap 0 R) θ) • f (circleMap 0 R θ)‖
        ≤ M * R * Real.exp (-(a * R) * Real.sin θ) := by
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    rw [norm_smul, norm_mul, norm_exp_mul_circleMap, deriv_circleMap, norm_mul,
      norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hR]
    have h1 := hM θ ⟨hθ.1.le, hθ.2⟩
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) hR.le)
      (Real.exp_pos (-(a * R) * Real.sin θ)).le]
  have hintb : IntervalIntegrable
      (fun θ => M * R * Real.exp (-(a * R) * Real.sin θ)) volume 0 π := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc ‖∫ θ in (0 : ℝ)..π, (Complex.exp (Complex.I * (a : ℂ) * circleMap 0 R θ) *
          deriv (circleMap 0 R) θ) • f (circleMap 0 R θ)‖
      ≤ ∫ θ in (0 : ℝ)..π, M * R * Real.exp (-(a * R) * Real.sin θ) :=
        intervalIntegral.norm_integral_le_of_norm_le Real.pi_nonneg hbound hintb
    _ = M * R * ∫ θ in (0 : ℝ)..π, Real.exp (-(a * R) * Real.sin θ) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ M * R * (π / (a * R)) :=
        mul_le_mul_of_nonneg_left (TauCeti.integral_exp_neg_mul_sin_le (a * R) (by positivity))
          (mul_nonneg hM0 hR.le)
    _ = π * M / a := by field_simp

/-- **The arc contribution vanishes.** Along any filter of radii on which `f` admits a sup bound
tending to `0` — the typical case `M R = 1/R` for `f z = z⁻¹` — the semicircular arc integral of
`f z · e^{iaz}` tends to `0`. This is the form the improper-integral limit consumes. -/
theorem tendsto_integral_semicircle_exp_mul_nhds_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {a : ℝ} {l : Filter ℝ}
    {M : ℝ → ℝ} (ha : 0 < a) (hpos : ∀ᶠ R in l, 0 ≤ R)
    (hM : ∀ᶠ R in l, ∀ θ ∈ Icc (0 : ℝ) π, ‖f (circleMap 0 R θ)‖ ≤ M R) (hM0 : Tendsto M l (𝓝 0)) :
    Tendsto (fun R => ∫ θ in (0 : ℝ)..π, (Complex.exp (Complex.I * (a : ℂ) * circleMap 0 R θ) *
        deriv (circleMap 0 R) θ) • f (circleMap 0 R θ)) l (𝓝 0) := by
  have hb : ∀ᶠ R in l, ‖∫ θ in (0 : ℝ)..π, (Complex.exp (Complex.I * (a : ℂ) *
      circleMap 0 R θ) * deriv (circleMap 0 R) θ) • f (circleMap 0 R θ)‖ ≤ π * M R / a := by
    filter_upwards [hpos, hM] with R hR hMR
    exact norm_integral_semicircle_exp_mul_le ha hR hMR
  exact squeeze_zero_norm' hb (by simpa using (hM0.const_mul π).div_const a)

end TauCeti.Contour

end

end
