/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Curve.ExcisionMeasure
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

/-!
# The excision leaves the arc's full length in the limit

The valence formula integrates over the fundamental-domain boundary with the integrand excised
within `ε` of the elliptic points. On the arc the excised integral turns out to be a constant
multiple of the *length* of the surviving parameter set, so its `ε → 0` limit is governed by
that length alone.

This file supplies the limit. The arc runs once around a `π/3` sector of the unit circle, so it
meets each excision centre at most once, and
`TauCeti.Contour.tendsto_intervalIntegral_excisionIndicator` applies with the whole length `2`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development; this file adapts the arc-specific half of
  `ForMathlib/ValenceFormula/PVChain/ArcContribution.lean`
  (`arc_preimage_subsingleton` and the specialisation of `arc_non_excluded_measure_tendsto`)
  onto the current Mathlib pin.

## Main results

* `TauCeti.ModularForm.injOn_fdBoundary_arc`: the arc is traversed injectively.
* `TauCeti.ModularForm.tendsto_intervalIntegral_excisionIndicator_fdBoundary_arc`: the surviving
  length of `[1, 3]` tends to `2` as `ε → 0⁺`.
-/

public section

open Filter Set Topology

namespace TauCeti

namespace ModularForm

/-- **The arc is traversed injectively.** On `[1, 3]` the boundary runs through the angles
`[π/3, 2π/3]` of the unit circle — less than one full turn — so `circleMap` is injective there
and distinct parameters give distinct points. -/
theorem injOn_fdBoundary_arc (H : ℝ) : InjOn (fdBoundary H) (Icc 1 3) := by
  have hpi := Real.pi_pos
  have hcm : InjOn (circleMap 0 1) (Ioc 0 (2 * Real.pi)) := by
    rw [← uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    exact injOn_circleMap_of_abs_sub_le one_ne_zero
      (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
  have hmem : ∀ {t : ℝ}, t ∈ Icc (1 : ℝ) 3 → (t + 1) * (Real.pi / 6) ∈ Ioc 0 (2 * Real.pi) :=
    fun ht => ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  intro t₁ h₁ t₂ h₂ heq
  rw [eqOn_fdBoundary_arc H h₁, eqOn_fdBoundary_arc H h₂] at heq
  nlinarith [hcm (hmem h₁) (hmem h₂) heq]

/-- **The excision leaves the arc's full length in the limit.** Deleting from `[1, 3]` the times
at which the boundary comes within `ε` of one of finitely many centres costs no length as
`ε → 0⁺`: the surviving length tends to `2`. -/
theorem tendsto_intervalIntegral_excisionIndicator_fdBoundary_arc (H : ℝ) (S : Finset ℂ) :
    Tendsto (fun ε => ∫ t in (1 : ℝ)..3,
        if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then (0 : ℝ) else 1) (𝓝[>] 0) (𝓝 2) := by
  have h := Contour.tendsto_intervalIntegral_excisionIndicator (continuous_fdBoundary H).measurable
    (by norm_num : (1 : ℝ) ≤ 3) S
    (Contour.measure_setOf_mem_eq_zero_of_injOn (injOn_fdBoundary_arc H) S)
  norm_num at h
  exact h

end ModularForm

end TauCeti
