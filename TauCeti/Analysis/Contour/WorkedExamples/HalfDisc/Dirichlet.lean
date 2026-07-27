/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.JordanLemma
public import TauCeti.Analysis.Contour.Residue.SimplePole
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.HalfResidue

/-!
# An improper integral evaluated by the generalized residue theorem

The Hungerbühler–Wasem motivating example: the integrand `e^{iaz} / z` (`a > 0`) has a simple
pole sitting **on** the contour, so the classical residue theorem does not apply, and the
integral along the real axis exists only as a Cauchy principal value.

Running the half-disc contour of `HalfDisc/Basic.lean` and letting the radius grow:

* the half-residue theorem gives `∮ = π i · Res₀ f` — half the enclosed-pole answer, because the
  generalized winding number at a smooth crossing is `½`;
* `hasCauchyPV_realSegment_diameter` subtracts the arc and restates the result along the real
  line, leaving the segment alone;
* Jordan's lemma kills the arc as `R → ∞`, since `‖1/z‖ = 1/R → 0` on it.

The oscillatory factor is essential rather than cosmetic: for `f z = z⁻¹` alone (`a = 0`) the
arc integral is `i π` for **every** `R` and never vanishes, so no limit exists to take. That is
exactly the regime the naive `ML` bound cannot reach and Jordan's lemma can.

## Main results

* `TauCeti.Contour.residue_exp_mul_I_div_self` — `Res₀ (e^{iaz}/z) = 1`, for every frequency.
* `TauCeti.Contour.neg_one_le_meromorphicOrderAt_dirichletIntegrand` — the pole is at worst
  simple, the hypothesis the half-residue theorem consumes.
* `TauCeti.Contour.hasCauchyPV_realSegment_dirichlet` — for each radius, the principal value
  along `[-R, R]` on the real axis is `π i` minus the arc contribution.
* `TauCeti.Contour.tendsto_integral_arc_dirichlet_atTop` — the arc contribution vanishes, by
  Jordan's lemma at `a = 1`.
* `TauCeti.Contour.tendsto_diameter_halfDiscBoundary_dirichlet` — hence the diameter principal
  values converge to `π i`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Thm 3.3.
-/

public section

noncomputable section

open Complex Filter Topology Set

namespace TauCeti.Contour

/-- The oscillatory Dirichlet integrand `e^{iaz} / z`, for a frequency `a`. -/
def dirichletIntegrand (a : ℝ) (z : ℂ) : ℂ := Complex.exp (Complex.I * (a : ℂ) * z) / z

theorem dirichletIntegrand_eq (a : ℝ) (z : ℂ) :
    dirichletIntegrand a z = Complex.exp (Complex.I * (a : ℂ) * z) * z⁻¹ := by
  rw [dirichletIntegrand, div_eq_mul_inv]

theorem meromorphicAt_dirichletIntegrand (a : ℝ) :
    MeromorphicAt (dirichletIntegrand a) 0 := by
  have h : MeromorphicAt (fun z : ℂ => Complex.exp (Complex.I * (a : ℂ) * z) * z⁻¹) 0 :=
    (((analyticAt_cexp (z := Complex.I * (a : ℂ) * 0)).comp
      (analyticAt_const.mul analyticAt_id)).meromorphicAt).mul
      (analyticAt_id.meromorphicAt.inv)
  exact h.congr (Filter.Eventually.of_forall fun z => (dirichletIntegrand_eq a z).symm)

/-- Near the origin `z · e^{iz}/z = e^{iz} → 1`. This single limit yields both the residue and
the simplicity of the pole. -/
theorem tendsto_sub_mul_dirichletIntegrand (a : ℝ) :
    Tendsto (fun z : ℂ => (z - 0) * dirichletIntegrand a z) (𝓝[≠] 0) (𝓝 1) := by
  have hlim : Tendsto (fun z : ℂ => Complex.exp (Complex.I * (a : ℂ) * z)) (𝓝[≠] 0) (𝓝 1) := by
    have hc : Continuous fun z : ℂ => Complex.exp (Complex.I * (a : ℂ) * z) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℂ))).continuousWithinAt.tendsto
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  rw [dirichletIntegrand_eq, sub_zero]
  field_simp

/-- **The residue of `e^{iz}/z` at the origin is `1`.** -/
theorem residue_exp_mul_I_div_self (a : ℝ) : residue (dirichletIntegrand a) 0 = 1 :=
  residue_eq_of_tendsto_sub_mul (meromorphicAt_dirichletIntegrand a)
    (tendsto_sub_mul_dirichletIntegrand a)

/-- The Dirichlet integrand is holomorphic away from the origin. -/
theorem differentiableOn_dirichletIntegrand (a : ℝ) :
    DifferentiableOn ℂ (dirichletIntegrand a) (univ \ {0}) := by
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz.2
  refine (DifferentiableAt.div ?_ differentiableAt_id hz0).differentiableWithinAt
  exact (Complex.differentiable_exp _).comp z (by fun_prop)

/-- **The pole at the origin is at worst simple.** Multiplying by `z` gives a function with a
limit there, so the order of `e^{iz}/z` is at least `-1` — the hypothesis the half-residue
theorem consumes. -/
theorem neg_one_le_meromorphicOrderAt_dirichletIntegrand (a : ℝ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (dirichletIntegrand a) 0 := by
  have hid : MeromorphicAt (fun z : ℂ => z - 0) 0 :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hprod : meromorphicOrderAt (fun z : ℂ => (z - 0) * dirichletIntegrand a z) 0
      = 1 + meromorphicOrderAt (dirichletIntegrand a) 0 := by
    have h := meromorphicOrderAt_mul hid (meromorphicAt_dirichletIntegrand a)
    rwa [meromorphicOrderAt_id_sub_const] at h
  have hnn : 0 ≤ meromorphicOrderAt (fun z : ℂ => (z - 0) * dirichletIntegrand a z) 0 :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg
      (hid.mul (meromorphicAt_dirichletIntegrand a))).1 ⟨1, tendsto_sub_mul_dirichletIntegrand a⟩
  rw [hprod] at hnn
  induction hord : meromorphicOrderAt (dirichletIntegrand a) 0 using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
      rw [hord] at hnn
      norm_cast at hnn ⊢
      omega

/-- **The identity along the real segment.** For each positive radius the principal value of
`e^{iaz}/z` along `[-R, R]` on the real axis is `π i` minus the arc contribution. The pole sits on
the path of integration, so this is a genuine principal value, not an ordinary integral. -/
theorem hasCauchyPV_realSegment_dirichlet (a : ℝ) {R : ℝ} (hR : 0 < R) :
    HasCauchyPV (fun t : ℝ => (t : ℂ)) (-R) R (dirichletIntegrand a)
      ((Real.pi : ℂ) * Complex.I -
        ∫ θ in (0 : ℝ)..Real.pi,
          dirichletIntegrand a (circleMap 0 R θ) * deriv (circleMap 0 R) θ) := by
  simpa [residue_exp_mul_I_div_self a] using
    hasCauchyPV_realSegment_diameter hR (differentiableOn_dirichletIntegrand a)
      (meromorphicAt_dirichletIntegrand a) (neg_one_le_meromorphicOrderAt_dirichletIntegrand a)

/-- **The arc contribution vanishes** for a positive frequency. This is Jordan's lemma: on the
semicircle the amplitude bound is `‖1/z‖ = 1/R → 0`, which the naive `ML` bound could not
exploit. -/
theorem tendsto_integral_arc_dirichlet_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ θ in (0 : ℝ)..Real.pi,
      dirichletIntegrand a (circleMap 0 R θ) * deriv (circleMap 0 R) θ) atTop (𝓝 0) := by
  refine (tendsto_integral_semicircle_exp_div_atTop_nhds_zero (a := a) ha).congr fun R => ?_
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [dirichletIntegrand_eq]
  ring

/-- **The improper limit.** As the radius grows, the diameter principal values converge to `π i`
— the half-residue, evaluated by the Hungerbühler–Wasem theorem on a contour through the pole,
where the classical residue theorem does not apply. -/
theorem tendsto_diameter_halfDiscBoundary_dirichlet {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => (Real.pi : ℂ) * Complex.I -
      ∫ θ in (0 : ℝ)..Real.pi,
        dirichletIntegrand a (circleMap 0 R θ) * deriv (circleMap 0 R) θ)
      atTop (𝓝 ((Real.pi : ℂ) * Complex.I)) := by
  simpa using tendsto_const_nhds.sub (tendsto_integral_arc_dirichlet_atTop ha)

end TauCeti.Contour

end

end
