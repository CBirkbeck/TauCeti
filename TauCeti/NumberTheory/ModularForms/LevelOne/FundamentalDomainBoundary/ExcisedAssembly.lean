/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Assembly

import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# The excised boundary contour integral of a level-one logarithmic derivative

`TauCeti.ModularForm.intervalIntegral_logDeriv_fdBoundary` assembles the boundary integral
for a form with no zeros on the contour. The valence formula needs the version that
tolerates them: the elliptic points `i` and `ρ` sit *on* the fundamental-domain boundary, so
a form vanishing there makes `logDeriv f` blow up on the contour itself and the integral only
exists as a principal value. The device is `ε`-excision — the integrand is replaced by `0`
within `ε` of any excision centre — and the excised assembly is what survives.

The three pieces are already available and each already tolerates the excision: the verticals
cancel by periodicity (`intervalIntegral_excised_fdBoundary_segment4_eq_neg_segment1`), the
arc collapses to its weight term
(`two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc`), and
the ceiling is untouched by the excision altogether
(`intervalIntegral_excised_logDeriv_fdBoundary_segment5_eq_qExpansionOrderAtCusp`).

## Main declarations

* `TauCeti.ModularForm.intervalIntegral_excised_logDeriv_fdBoundary`: the assembled excised
  boundary integral, `2πi · ord_∞ - (k/2) · ∫₁³ (excised logDeriv γ)`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Assembly.lean`) this file ports onto the
  current Mathlib pin.
-/

public section

open Complex Function MeasureTheory Set UpperHalfPlane

open scoped MatrixGroups Real

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- **The excised boundary contour integral of a level-one logarithmic derivative.** The
four pieces assemble exactly as they do without the excision: the verticals cancel, the arc
collapses to its weight term, and the ceiling reads the cusp order. What the excision buys is
that none of this needs `f` to be nonvanishing *on* the contour — the elliptic points sit
there, and the excision is what lets the integral exist as a principal value around them.

Compare `intervalIntegral_logDeriv_fdBoundary`, the unexcised assembly, whose arc term is the
constant `k·(π/6)·i`: here the arc term is `(k/2)` times the excised arc integral of the
contour's own logarithmic derivative, which tends to that constant as `ε → 0`. -/
theorem intervalIntegral_excised_logDeriv_fdBoundary [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H ε : ℝ} {S : Finset ℂ}
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hrefl : ∀ s ∈ S, -(starRingEnd ℂ) s ∈ S) (hε : ε < H - 1)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0)
    (hint01 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 0 1)
    (hint12 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 1 2)
    (hint23 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 2 3)
    (hint34 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 3 4)
    (hint45 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 4 5) :
    ∫ t in (0 : ℝ)..5, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) =
      2 * Real.pi * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) / 2 * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
          else logDeriv (fdBoundary H) t) := by
  have hint13 := hint12.trans hint23
  have hint35 := hint34.trans hint45
  have hvert : (∫ t in (3 : ℝ)..4, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t))) =
      -∫ t in (0 : ℝ)..1, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) := by
    simpa only [smul_ite, smul_zero] using
      intervalIntegral_excised_fdBoundary_segment4_eq_neg_segment1 H
        (TauCeti.Function.Periodic.logDeriv hper) hrefl
  rw [← intervalIntegral.integral_add_adjacent_intervals hint01 (hint13.trans hint35),
    ← intervalIntegral.integral_add_adjacent_intervals hint13 hint35,
    ← intervalIntegral.integral_add_adjacent_intervals hint34 hint45,
    hvert, intervalIntegral_excised_logDeriv_fdBoundary_segment5_eq_qExpansionOrderAtCusp
      hnorm hε hper hga hgz]
  linear_combination
    two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc
      f hS hnorm hinv hd hne hint12 / 2

end ModularForm

end TauCeti
