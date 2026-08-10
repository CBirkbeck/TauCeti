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
the ceiling is untouched by the excision altogether: the excision centres lie on the unit
circle while the ceiling runs at height `H`, so no ceiling point is within `ε` of one once
`ε < H - 1`.

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

/-- **The excision never fires on the ceiling.** The excision centres lie on the unit circle,
so their heights are at most `1`, while the ceiling runs at height `H`; once `ε < H - 1` no
ceiling point is within `ε` of a centre. -/
theorem not_exists_dist_le_of_mem_Icc_four_five {H ε : ℝ} {S : Finset ℂ}
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hε : ε < H - 1) {t : ℝ} (ht : t ∈ Icc (4 : ℝ) 5) :
    ¬ ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε := by
  rintro ⟨s, hs, hle⟩
  have hsim : |s.im| ≤ 1 := (Complex.abs_im_le_norm s).trans (hnorm s hs).le
  have himle : |(fdBoundary H t - s).im| ≤ ‖fdBoundary H t - s‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, im_fdBoundary_segment5 H ht] at himle
  have : H - s.im ≤ ε := (le_abs_self _).trans (himle.trans hle)
  cases abs_le.mp hsim
  linarith

/-- **The excised ceiling integral is the plain one.** The excision never fires on the
ceiling, so the excised integrand agrees with the unexcised one there and the ceiling still
evaluates through the `q`-circle to `2πi · ord_∞`. -/
theorem intervalIntegral_excised_fdBoundary_segment5 {g : ℍ → ℂ} {H ε : ℝ} {S : Finset ℂ}
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hε : ε < H - 1)
    (hper : Function.Periodic (g ∘ ofComplex) 1)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 g) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 g q ≠ 0) :
    ∫ t in (4 : ℝ)..5, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (g ∘ ofComplex) (fdBoundary H t)) =
      2 * Real.pi * Complex.I * qExpansionOrderAtCusp 1 g := by
  rw [intervalIntegral.integral_congr (g := fun t ↦ deriv (fdBoundary H) t •
        logDeriv (g ∘ ofComplex) (fdBoundary H t)) fun t ht ↦ ?_,
    (intervalIntegral_fdBoundary_segment5_eq_circleIntegral_logDeriv_cuspFunction hper).trans
      (circleIntegral_logDeriv_cuspFunction hga hgz)]
  rw [uIcc_of_le (by norm_num : (4 : ℝ) ≤ 5)] at ht
  exact if_neg (not_exists_dist_le_of_mem_Icc_four_five hnorm hε ht)

/-- The excision commutes with the scalar multiplication by `deriv γ`: excising the whole
integrand is excising the function it is built from. -/
private lemma excised_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H ε : ℝ}
    {S : Finset ℂ} {φ : ℂ → E} (t : ℝ) :
    (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • φ (fdBoundary H t)) =
    deriv (fdBoundary H) t •
      (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0 else φ (fdBoundary H t)) := by
  split <;> simp

/-- **The excised integrals over the two verticals cancel.** The left vertical is the right
one translated by `1` and traversed backwards, and the excision set is stable under the
reflection matching them, so the excision does not disturb the cancellation.

This is `intervalIntegral_excised_fdBoundary_segment4_eq_neg_segment1` read on the
integrand shape the arc pairing uses, with the excision outside the scalar multiplication
rather than inside it. -/
theorem intervalIntegral_excised_deriv_smul_fdBoundary_segment4_eq_neg_segment1 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (H : ℝ) {φ : ℂ → E} (hφ : Function.Periodic φ 1)
    {S : Finset ℂ} {ε : ℝ} (hrefl : ∀ s ∈ S, -(starRingEnd ℂ) s ∈ S) :
    (∫ t in (3 : ℝ)..4, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • φ (fdBoundary H t))) =
      -∫ t in (0 : ℝ)..1, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • φ (fdBoundary H t)) := by
  simp only [excised_smul]
  exact intervalIntegral_excised_fdBoundary_segment4_eq_neg_segment1 H hφ hrefl

/-- **The excised arc integral is the weight term.** Halving the arc-pairing identity
`2·∫ = -k·∫`, which is the form the assembly consumes: the arc contributes `-(k/2)` times
the arc integral of the contour's own logarithmic derivative. -/
theorem intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ}
    {ε : ℝ} (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hint : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 1 2) :
    ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) =
      -(k : ℂ) / 2 * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else logDeriv (fdBoundary H) t) := by
  have h := two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc
    f hS hnorm hinv hd hne hint
  linear_combination h / 2

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
  rw [← intervalIntegral.integral_add_adjacent_intervals hint01 (hint13.trans hint35),
    ← intervalIntegral.integral_add_adjacent_intervals hint13 hint35,
    ← intervalIntegral.integral_add_adjacent_intervals hint34 hint45,
    intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc f hS hnorm hinv
      hd hne hint12,
    intervalIntegral_excised_deriv_smul_fdBoundary_segment4_eq_neg_segment1 H
      (TauCeti.Function.Periodic.logDeriv hper) hrefl,
    intervalIntegral_excised_fdBoundary_segment5 hnorm hε hper hga hgz]
  ring

end ModularForm

end TauCeti
