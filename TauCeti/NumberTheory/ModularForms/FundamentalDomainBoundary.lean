/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# The boundary contour of the standard fundamental domain

The five-segment boundary of the truncated standard fundamental domain for `SL(2, ℤ)`,
parameterized over `[0, 5]` at a variable height `H`: the right vertical from `1/2 + H·i`
down to `ρ + 1`, the unit-circle arcs from `ρ + 1` to `i` and from `i` to `ρ`, the left
vertical from `ρ` up to `-1/2 + H·i`, and the top horizontal back to the start. The corner
values and closedness recorded here are the anchors of the valence-formula contour.

## Main declarations

* `TauCeti.ModularForm.fdBoundary` (with the segments `fdBoundary_seg1` … `fdBoundary_seg5`).
* `TauCeti.ModularForm.fdBoundary_at_three`: the parameter `3` lands on `ρ`.
* `TauCeti.ModularForm.fdBoundary_closed`: the contour is closed.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open Complex UpperHalfPlane

open scoped Real

namespace TauCeti

namespace ModularForm

/-- Segment 1: the right vertical from `1/2 + H·i` down to `ρ + 1`, over `t ∈ [0, 1]`. -/
def fdBoundary_seg1 (H : ℝ) : ℝ → ℂ := fun t ↦
  1 / 2 + (H - t * (H - Real.sqrt 3 / 2)) * Complex.I

/-- Segment 2: the unit-circle arc from `ρ + 1` to `i` (angle `π/3 → π/2`), over
`t ∈ [1, 2]`. -/
def fdBoundary_seg2 : ℝ → ℂ := fun t ↦
  Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * Complex.I)

/-- Segment 3: the unit-circle arc from `i` to `ρ` (angle `π/2 → 2π/3`), over
`t ∈ [2, 3]`. -/
def fdBoundary_seg3 : ℝ → ℂ := fun t ↦
  Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * Complex.I)

/-- Segment 4: the left vertical from `ρ` up to `-1/2 + H·i`, over `t ∈ [3, 4]`. -/
def fdBoundary_seg4 (H : ℝ) : ℝ → ℂ := fun t ↦
  -1 / 2 + (Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2)) * Complex.I

/-- Segment 5: the top horizontal from `-1/2 + H·i` to `1/2 + H·i`, over `t ∈ [4, 5]`. -/
def fdBoundary_seg5 (H : ℝ) : ℝ → ℂ := fun t ↦ (t - 9 / 2) + H * Complex.I

/-- The boundary of the standard fundamental domain truncated at height `H`, as a closed
contour parameterized over `[0, 5]`. -/
def fdBoundary (H : ℝ) : ℝ → ℂ := fun t ↦
  if t ≤ 1 then fdBoundary_seg1 H t
  else if t ≤ 2 then fdBoundary_seg2 t
  else if t ≤ 3 then fdBoundary_seg3 t
  else if t ≤ 4 then fdBoundary_seg4 H t
  else fdBoundary_seg5 H t

/-- The interior partition points of the five-segment parameterization. -/
def fdBoundaryPartition : Finset ℝ := {1, 2, 3, 4}

@[simp]
lemma fdBoundary_at_zero (H : ℝ) : fdBoundary H 0 = 1 / 2 + H * Complex.I := by
  simp [fdBoundary, fdBoundary_seg1]

lemma fdBoundary_at_one (H : ℝ) : fdBoundary H 1 = (ρ : ℂ) + 1 := by
  simp only [fdBoundary, le_refl, ite_true, fdBoundary_seg1]
  rw [Complex.ext_iff]
  refine ⟨by simp [ρ]; norm_num, ?_⟩
  simp [ρ]

lemma fdBoundary_at_two (H : ℝ) : fdBoundary H 2 = Complex.I := by
  simp only [fdBoundary, show ¬(2 : ℝ) ≤ 1 by norm_num, le_refl, ite_true, ite_false,
    fdBoundary_seg2]
  have hA : ((Real.pi : ℂ) / 3 + (((2 : ℝ) : ℂ) - 1) * ((Real.pi : ℂ) / 2 -
      (Real.pi : ℂ) / 3)) * Complex.I = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hA, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

lemma fdBoundary_at_three (H : ℝ) : fdBoundary H 3 = (ρ : ℂ) := by
  simp only [fdBoundary, show ¬(3 : ℝ) ≤ 1 by norm_num, show ¬(3 : ℝ) ≤ 2 by norm_num,
    le_refl, ite_true, ite_false, fdBoundary_seg3]
  have hA : ((Real.pi : ℂ) / 2 + (((3 : ℝ) : ℂ) - 2) * (2 * (Real.pi : ℂ) / 3 -
      (Real.pi : ℂ) / 2)) * Complex.I = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hB : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [hA, exp_mul_I, ← ofReal_cos, ← ofReal_sin, hB, Real.cos_pi_sub, Real.cos_pi_div_three,
    Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [Complex.ext_iff]
  refine ⟨by simp [ρ]; norm_num, ?_⟩
  simp [ρ]

lemma fdBoundary_at_four (H : ℝ) : fdBoundary H 4 = -1 / 2 + H * Complex.I := by
  simp only [fdBoundary, show ¬(4 : ℝ) ≤ 1 by norm_num, show ¬(4 : ℝ) ≤ 2 by norm_num,
    show ¬(4 : ℝ) ≤ 3 by norm_num, le_refl, ite_true, ite_false, fdBoundary_seg4]
  push_cast
  ring

@[simp]
lemma fdBoundary_at_five (H : ℝ) : fdBoundary H 5 = 1 / 2 + H * Complex.I := by
  simp only [fdBoundary, show ¬(5 : ℝ) ≤ 1 by norm_num, show ¬(5 : ℝ) ≤ 2 by norm_num,
    show ¬(5 : ℝ) ≤ 3 by norm_num, show ¬(5 : ℝ) ≤ 4 by norm_num, ite_false,
    fdBoundary_seg5]
  push_cast
  ring

/-- The boundary contour is closed. -/
lemma fdBoundary_closed (H : ℝ) : fdBoundary H 5 = fdBoundary H 0 := by
  rw [fdBoundary_at_five, fdBoundary_at_zero]

end ModularForm

end TauCeti

end
