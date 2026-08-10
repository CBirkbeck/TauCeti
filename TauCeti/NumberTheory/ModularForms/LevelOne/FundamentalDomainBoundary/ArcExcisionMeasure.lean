/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.ExcisionMeasure
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

## Main results

* `TauCeti.ModularForm.injOn_fdBoundary_arc`: the arc is traversed injectively.
* `TauCeti.ModularForm.tendsto_intervalIntegral_excisionIndicator_fdBoundary_arc`: the surviving
  length of `[1, 3]` tends to `2` as `ε → 0⁺`.
-/

public section

open Filter Set Topology

namespace TauCeti

namespace ModularForm

/-- **The arc is traversed injectively.** On `[1, 3]` the boundary runs once through the angles
`[π/3, 2π/3]` of the unit circle, an interval on which `Real.cos` is injective, so distinct
parameters give distinct points. -/
theorem injOn_fdBoundary_arc (H : ℝ) : InjOn (fdBoundary H) (Icc 1 3) := by
  have hpi := Real.pi_pos
  have hmem : ∀ {t : ℝ}, t ∈ Icc (1 : ℝ) 3 → (t + 1) * (Real.pi / 6) ∈ Icc 0 Real.pi :=
    fun ht => ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  intro t₁ h₁ t₂ h₂ heq
  rw [eqOn_fdBoundary_arc H h₁, eqOn_fdBoundary_arc H h₂] at heq
  have hre := congrArg Complex.re heq
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul,
    Complex.exp_ofReal_mul_I_re] at hre
  have := Real.strictAntiOn_cos.injOn (hmem h₁) (hmem h₂) hre
  nlinarith [this]

/-- **The excision leaves the arc's full length in the limit.** Deleting from `[1, 3]` the times
at which the boundary comes within `ε` of one of finitely many centres costs no length as
`ε → 0⁺`: the surviving length tends to `2`. -/
theorem tendsto_intervalIntegral_excisionIndicator_fdBoundary_arc (H : ℝ) (S : Finset ℂ) :
    Tendsto (fun ε => ∫ t in (1 : ℝ)..3,
        if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then (0 : ℝ) else 1) (𝓝[>] 0) (𝓝 2) := by
  have h := Contour.tendsto_intervalIntegral_excisionIndicator (continuous_fdBoundary H)
    (by norm_num : (1 : ℝ) ≤ 3) (injOn_fdBoundary_arc H) S
  norm_num at h
  exact h

end ModularForm

end TauCeti
