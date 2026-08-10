/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Curve.ExcisedIntegrability
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.DerivBound
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Basic

import TauCeti.Analysis.Contour.LogDerivFTC

/-!
# The excised boundary integrand is integrable

`intervalIntegral_excised_logDeriv_fdBoundary` assembles the excised boundary integral from
integrability *assumed* on `[0, 1]`, `[1, 2]` and `[4, 5]`. This file discharges that assumption,
for any subinterval of `[0, 5]` at once.

Both inputs the general criterion needs are available for the boundary contour: its derivative is
globally bounded (`exists_norm_deriv_fdBoundary_le`), and off the excision the contour stays in
the open set where the form is analytic and nonvanishing, so its logarithmic derivative is
analytic there (`analyticAt_logDeriv_of_analyticAt`) and in particular continuous.

The hypotheses are exactly those of `hasCauchyPV_fdBoundary_logDeriv`, so one block of
assumptions serves both the excised assembly and the principal value it converges to.

## Main results

* `TauCeti.ModularForm.intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary`:
  the excised boundary integrand is interval-integrable on any subinterval of `[0, 5]`.
-/

public section

open Complex Filter MeasureTheory Set UpperHalfPlane

open scoped MatrixGroups Real

namespace TauCeti

namespace ModularForm

/-- **The excised boundary integrand is integrable.** Off the excision the contour stays in `U`,
where the form is analytic and nonvanishing, so its logarithmic derivative is continuous there;
with `deriv (fdBoundary H)` globally bounded, `TauCeti.Contour`'s criterion applies.

`hε` is needed to know that a point at distance `≥ ε` from every centre is not itself a centre. -/
theorem intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary {g : ℂ → ℂ}
    {H ε : ℝ} (hH : 1 ≤ H) (hε : 0 < ε) {S : Finset ℂ} {U : Set ℂ}
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ g z ∧ g z ≠ 0)
    {a b : ℝ} (hab : uIcc a b ⊆ Icc (0 : ℝ) 5) :
    IntervalIntegrable (fun t => if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv g (fdBoundary H t)) volume a b := by
  obtain ⟨M, -, hM⟩ := exists_norm_deriv_fdBoundary_le H
  have hφ : ContinuousOn (logDeriv g)
      (fdBoundary H '' (uIcc a b ∩ {t | ∀ s ∈ S, ε ≤ ‖fdBoundary H t - s‖})) := by
    rintro z ⟨t, ⟨ht, hfar⟩, rfl⟩
    have hmemU : fdBoundary H t ∈ U :=
      hUdom (fdBoundary_mem_coe_truncatedFundamentalDomain hH (hab ht))
    have hnotS : fdBoundary H t ∉ S := fun hs => by
      have := hfar _ hs
      rw [sub_self, norm_zero] at this
      exact absurd this (not_le.mpr hε)
    exact (Contour.analyticAt_logDeriv_of_analyticAt (hoff _ hmemU hnotS).1
      (hoff _ hmemU hnotS).2).continuousAt.continuousWithinAt
  simpa only [smul_eq_mul, mul_comm] using
    Contour.intervalIntegrable_excised_of_continuousOn (continuous_fdBoundary H) hM hφ

end ModularForm

end TauCeti
