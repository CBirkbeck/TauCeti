/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The vertical integrals of a periodic integrand cancel

The reflection `t ↦ 4 - t` carries the right vertical of the boundary contour onto the
left vertical through the translation `z ↦ z - 1`, reversing the orientation. For any
integrand `φ` of period `1` — the level-one situation, where `φ` is the logarithmic
derivative of the extension of a modular form — the left vertical contour integral of
`γ' • φ ∘ γ` is therefore the negative of the right one: the values are identified by
periodicity and the derivatives by the reflection, up to the orientation sign. The
statement is unconditional: the substitution and the interior congruence need no
integrability.

## Main declarations

* `TauCeti.ModularForm.intervalIntegral_fdBoundary_segment4_eq_neg_segment1`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Assembly.lean`, the vertical
  cancellation) this file ports onto the current Mathlib pin.
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace ModularForm

/-- The left vertical integral of a period-`1` integrand along the boundary contour is
the negative of the right vertical integral: the reflection `t ↦ 4 - t` carries the
right vertical onto the left through the translation `z ↦ z - 1`, which the periodicity
absorbs, and reverses the orientation. -/
theorem intervalIntegral_fdBoundary_segment4_eq_neg_segment1 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (H : ℝ) {φ : ℂ → E}
    (hφ : Function.Periodic φ 1) :
    ∫ t in (3 : ℝ)..4, deriv (fdBoundary H) t • φ (fdBoundary H t) =
      -∫ t in (0 : ℝ)..1, deriv (fdBoundary H) t • φ (fdBoundary H t) := by
  have hsub : (∫ t in (3 : ℝ)..4, deriv (fdBoundary H) t • φ (fdBoundary H t)) =
      ∫ u in (0 : ℝ)..1, deriv (fdBoundary H) (4 - u) • φ (fdBoundary H (4 - u)) := by
    have h41 : (4 : ℝ) - 1 = 3 := by norm_num
    have h40 : (4 : ℝ) - 0 = 4 := by norm_num
    have h := intervalIntegral_comp_fdBoundary_four_sub H φ (a := 0) (b := 1)
    rwa [h41, h40] at h
  rw [hsub, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun u hu ↦ ?_
  rw [fdBoundary_four_sub_vertical H ⟨hu.1.le, hu.2.le⟩,
    deriv_fdBoundary_four_sub_vertical H hu, hφ.sub_eq, neg_smul]

/-- The right-vertical integrability of a period-`1` integrand reflects to the left
vertical: the reflection carries the integrand to its negation through the translation
and the periodicity. -/
theorem intervalIntegrable_deriv_smul_fdBoundary_segment4 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {H : ℝ} {φ : ℂ → E}
    (hφ : Function.Periodic φ 1)
    (hint : IntervalIntegrable (fun t ↦ deriv (fdBoundary H) t • φ (fdBoundary H t))
      volume 0 1) :
    IntervalIntegrable (fun t ↦ deriv (fdBoundary H) t • φ (fdBoundary H t))
      volume 3 4 := by
  have hI := (hint.neg.comp_sub_left 4).symm
  have h41 : (4 : ℝ) - 1 = 3 := by norm_num
  have h40 : (4 : ℝ) - 0 = 4 := by norm_num
  rw [h40, h41] at hI
  refine hI.congr_uIoo ?_
  rw [Set.uIoo_of_le (by norm_num : (3 : ℝ) ≤ 4)]
  intro x hx
  have hu : 4 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hval := fdBoundary_four_sub_vertical H ⟨hu.1.le, hu.2.le⟩
  have hder := deriv_fdBoundary_four_sub_vertical H hu
  have hxx : (4 : ℝ) - (4 - x) = x := by ring
  rw [hxx] at hval hder
  have hval' : fdBoundary H (4 - x) = fdBoundary H x + 1 := by linear_combination -hval
  have hder' : deriv (fdBoundary H) (4 - x) = -deriv (fdBoundary H) x := by
    linear_combination hder
  simp only [Pi.neg_apply, hval', hder', hφ (fdBoundary H x), neg_smul, neg_neg]

/-- **The vertical cancellation survives excision.** The reflection `t ↦ 4 - t` carries the
right vertical onto the left through the translation `z ↦ z - 1`, so an integrand excised
within `ε` of a set closed under `s ↦ s ± 1` is excised at matching parameters on the two
verticals, and the cancellation of the untruncated integrals
(`TauCeti.ModularForm.intervalIntegral_fdBoundary_segment4_eq_neg_segment1`) persists.

Translation-closure of the excision set is exactly what
`TauCeti.ModularForm.verticalSingularSet` provides. -/
theorem intervalIntegral_truncated_fdBoundary_segment4_eq_neg_segment1 (H : ℝ) {φ : ℂ → ℂ}
    (hφ : Function.Periodic φ 1) {S : Finset ℂ} {ε : ℝ}
    (hadd : ∀ s ∈ S, s + 1 ∈ S) (hsub : ∀ s ∈ S, s - 1 ∈ S) :
    (∫ t in (3 : ℝ)..4, if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else φ (fdBoundary H t) * deriv (fdBoundary H) t) =
      -∫ t in (0 : ℝ)..1, if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else φ (fdBoundary H t) * deriv (fdBoundary H) t := by
  have hcomp : (∫ t in (3 : ℝ)..4, if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else φ (fdBoundary H t) * deriv (fdBoundary H) t) =
      ∫ u in (0 : ℝ)..1, if ∃ s ∈ S, ‖fdBoundary H (4 - u) - s‖ ≤ ε then 0
        else φ (fdBoundary H (4 - u)) * deriv (fdBoundary H) (4 - u) := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := 1) (d := (4 : ℝ))
      (fun t => if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then (0 : ℂ)
        else φ (fdBoundary H t) * deriv (fdBoundary H) t)
    norm_num at h
    exact h.symm
  rw [hcomp, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun u hu => ?_
  have hval : fdBoundary H (4 - u) = fdBoundary H u - 1 :=
    fdBoundary_four_sub_vertical H ⟨hu.1.le, hu.2.le⟩
  -- The excision test transports along the translation, in both directions.
  have hiff : (∃ s ∈ S, ‖fdBoundary H (4 - u) - s‖ ≤ ε) ↔
      ∃ s ∈ S, ‖fdBoundary H u - s‖ ≤ ε := by
    rw [hval]
    refine ⟨fun ⟨s, hs, hle⟩ => ⟨s + 1, hadd s hs, ?_⟩, fun ⟨s, hs, hle⟩ => ⟨s - 1, hsub s hs, ?_⟩⟩
    · rwa [show fdBoundary H u - (s + 1) = fdBoundary H u - 1 - s by ring]
    · rwa [show fdBoundary H u - 1 - (s - 1) = fdBoundary H u - s by ring]
  -- Split on the excision test before rewriting: the `ite`'s decidability instance mentions
  -- the condition, so rewriting inside it is not motive-correct.
  by_cases hc : ∃ s ∈ S, ‖fdBoundary H u - s‖ ≤ ε
  · rw [if_pos (hiff.mpr hc), if_pos hc, neg_zero]
  · rw [if_neg fun h => hc (hiff.mp h), if_neg hc, hval,
      deriv_fdBoundary_four_sub_vertical H hu, hφ.sub_eq]
    ring

end ModularForm

end TauCeti

end
