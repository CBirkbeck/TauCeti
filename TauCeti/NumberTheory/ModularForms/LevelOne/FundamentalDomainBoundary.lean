/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# The boundary contour of the standard fundamental domain

The raw five-segment path family `fdBoundary H`, parameterized over `[0, 5]` at a height
parameter `H`: the right vertical from `1/2 + H·i` through `ρ + 1`, the unit-circle arcs
from `ρ + 1` to `i` and from `i` to `ρ`, the left vertical from `ρ` through `-1/2 + H·i`,
and the closing top horizontal. For `1 < H` — so that the horizontal sits above the arc,
whose highest point is `i` — this is the boundary of the standard fundamental domain
truncated at height `H`; the definitions carry no hypothesis, and the boundary reading is
invoked with that bound downstream. The corner values and closedness recorded here are the
anchors of the valence-formula contour.

## Main declarations

* `TauCeti.ModularForm.fdBoundary` (with the segments `fdBoundary_seg1` … `fdBoundary_seg5`,
  built from `AffineMap.lineMap` and `circleMap`).
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

/-- Segment 1: the right vertical from `1/2 + H·i` through `ρ + 1`, over `t ∈ [0, 1]`. -/
def fdBoundary_seg1 (H : ℝ) : ℝ → ℂ := fun t ↦
  AffineMap.lineMap (1 / 2 + H * Complex.I) ((ρ : ℂ) + 1) t

/-- Segment 2: the unit-circle arc from `ρ + 1` to `i` (angle `π/3 → π/2`), over
`t ∈ [1, 2]`. -/
def fdBoundary_seg2 : ℝ → ℂ := fun t ↦
  circleMap 0 1 (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))

/-- Segment 3: the unit-circle arc from `i` to `ρ` (angle `π/2 → 2π/3`), over
`t ∈ [2, 3]`. -/
def fdBoundary_seg3 : ℝ → ℂ := fun t ↦
  circleMap 0 1 (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))

/-- Segment 4: the left vertical from `ρ` through `-1/2 + H·i`, over `t ∈ [3, 4]`. -/
def fdBoundary_seg4 (H : ℝ) : ℝ → ℂ := fun t ↦
  AffineMap.lineMap (ρ : ℂ) (-1 / 2 + H * Complex.I) (t - 3)

/-- Segment 5: the top horizontal from `-1/2 + H·i` to `1/2 + H·i`, over `t ∈ [4, 5]`. -/
def fdBoundary_seg5 (H : ℝ) : ℝ → ℂ := fun t ↦
  AffineMap.lineMap (-1 / 2 + H * Complex.I) (1 / 2 + H * Complex.I) (t - 4)

/-- The raw five-segment path at height parameter `H`, parameterized over `[0, 5]` and
closed for every `H`. For `1 < H` it is the boundary of the standard fundamental domain
truncated at height `H`. -/
def fdBoundary (H : ℝ) : ℝ → ℂ := fun t ↦
  if t ≤ 1 then fdBoundary_seg1 H t
  else if t ≤ 2 then fdBoundary_seg2 t
  else if t ≤ 3 then fdBoundary_seg3 t
  else if t ≤ 4 then fdBoundary_seg4 H t
  else fdBoundary_seg5 H t

/-- The interior breakpoints of the five-segment parameterization. -/
def fdBoundaryBreakpoints : Finset ℝ := {1, 2, 3, 4}

/-- Membership in the breakpoints is being one of the four interior corners. -/
@[simp]
lemma mem_fdBoundaryBreakpoints {t : ℝ} :
    t ∈ fdBoundaryBreakpoints ↔ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by
  unfold fdBoundaryBreakpoints
  simp

section Branches

variable {H t : ℝ}

/-- On `t ≤ 1` the path follows segment 1. -/
lemma fdBoundary_of_le_one (ht : t ≤ 1) : fdBoundary H t = fdBoundary_seg1 H t := by
  unfold fdBoundary
  rw [if_pos ht]

/-- On `1 < t ≤ 2` the path follows segment 2. -/
lemma fdBoundary_of_le_two (h1 : 1 < t) (h2 : t ≤ 2) : fdBoundary H t = fdBoundary_seg2 t := by
  unfold fdBoundary
  rw [if_neg (not_le.mpr h1), if_pos h2]

/-- On `2 < t ≤ 3` the path follows segment 3. -/
lemma fdBoundary_of_le_three (h2 : 2 < t) (h3 : t ≤ 3) :
    fdBoundary H t = fdBoundary_seg3 t := by
  unfold fdBoundary
  rw [if_neg (by linarith : ¬t ≤ 1), if_neg (not_le.mpr h2), if_pos h3]

/-- On `3 < t ≤ 4` the path follows segment 4. -/
lemma fdBoundary_of_le_four (h3 : 3 < t) (h4 : t ≤ 4) :
    fdBoundary H t = fdBoundary_seg4 H t := by
  unfold fdBoundary
  rw [if_neg (by linarith : ¬t ≤ 1), if_neg (by linarith : ¬t ≤ 2),
    if_neg (not_le.mpr h3), if_pos h4]

/-- On `4 < t` the path follows segment 5. -/
lemma fdBoundary_of_lt_four (h4 : 4 < t) : fdBoundary H t = fdBoundary_seg5 H t := by
  unfold fdBoundary
  rw [if_neg (by linarith : ¬t ≤ 1), if_neg (by linarith : ¬t ≤ 2),
    if_neg (by linarith : ¬t ≤ 3), if_neg (not_le.mpr h4)]

end Branches

/-- The path starts at the top right corner `1/2 + H·i`. -/
@[simp]
lemma fdBoundary_at_zero (H : ℝ) : fdBoundary H 0 = 1 / 2 + H * Complex.I := by
  rw [fdBoundary_of_le_one (by norm_num), fdBoundary_seg1, AffineMap.lineMap_apply_zero]

/-- The parameter `1` lands on the corner `ρ + 1`. -/
@[simp]
lemma fdBoundary_at_one (H : ℝ) : fdBoundary H 1 = (ρ : ℂ) + 1 := by
  rw [fdBoundary_of_le_one le_rfl, fdBoundary_seg1, AffineMap.lineMap_apply_one]

/-- The parameter `2` lands on `i`. -/
@[simp]
lemma fdBoundary_at_two (H : ℝ) : fdBoundary H 2 = Complex.I := by
  rw [fdBoundary_of_le_two (by norm_num) le_rfl, fdBoundary_seg2,
    show (Real.pi / 3 + ((2 : ℝ) - 1) * (Real.pi / 2 - Real.pi / 3)) = Real.pi / 2 by ring,
    circleMap, Complex.ofReal_one, one_mul, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- The parameter `3` lands on the elliptic corner `ρ`. -/
@[simp]
lemma fdBoundary_at_three (H : ℝ) : fdBoundary H 3 = (ρ : ℂ) := by
  rw [fdBoundary_of_le_three (by norm_num) le_rfl, fdBoundary_seg3,
    show (Real.pi / 2 + ((3 : ℝ) - 2) * (2 * Real.pi / 3 - Real.pi / 2)) =
      2 * Real.pi / 3 by ring,
    circleMap, Complex.ofReal_one, one_mul, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [Complex.ext_iff]
  refine ⟨by simp [ρ]; norm_num, ?_⟩
  simp [ρ]

/-- The parameter `4` lands on the top left corner `-1/2 + H·i`. -/
@[simp]
lemma fdBoundary_at_four (H : ℝ) : fdBoundary H 4 = -1 / 2 + H * Complex.I := by
  rw [fdBoundary_of_le_four (by norm_num) le_rfl, fdBoundary_seg4,
    show (4 : ℝ) - 3 = 1 by norm_num, AffineMap.lineMap_apply_one]

/-- The path ends where it starts, at `1/2 + H·i`. -/
@[simp]
lemma fdBoundary_at_five (H : ℝ) : fdBoundary H 5 = 1 / 2 + H * Complex.I := by
  rw [fdBoundary_of_lt_four (by norm_num), fdBoundary_seg5,
    show (5 : ℝ) - 4 = 1 by norm_num, AffineMap.lineMap_apply_one]

/-- The boundary contour is closed. -/
lemma fdBoundary_closed (H : ℝ) : fdBoundary H 5 = fdBoundary H 0 := by
  rw [fdBoundary_at_five, fdBoundary_at_zero]

end ModularForm

end TauCeti

end
