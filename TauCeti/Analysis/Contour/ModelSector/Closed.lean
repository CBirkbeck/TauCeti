/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.ModelSector.Corner
public import TauCeti.Analysis.Contour.Winding.Number.Circle
public import TauCeti.Analysis.Contour.Winding.Number.Concat
public import TauCeti.Analysis.Contour.Winding.Number.Reparam

/-!
# The Hungerbühler–Wasem model sector

For `0 < r` and `0 ≤ α`, the model sector of opening angle `α` at `z₀` is the closed curve made of
a radial segment into `z₀`, a circular arc of radius `r` sweeping `α`, and a radial segment back
out. (The definition itself accepts any `r` and `α`; outside those bounds the two parameter
intervals reverse and the description below does not apply.) Its generalized
winding number about its own corner is `α / 2π` — the value HW (2.4) attaches to a corner of
interior angle `α`, and the source of the `½` at a smooth crossing and the `1/6` at a `π/3` corner.

The two radial segments are packaged as a single `twoRayCorner`, since neither has a principal
value on its own; the arc is a reparametrised `circleMap`. Concatenating them, the curve is
traversed from the far end of one radius rather than from the corner.

## Main definitions

* `TauCeti.Contour.modelSector` — the model sector, on `[-r, r + α]` with the corner at parameter
  `0`; closed when `0 < r` and `0 ≤ α`.

## Main results

* `TauCeti.Contour.windingNumber_modelSector_eq` — its winding number about `z₀` is `α / 2π`.
* `TauCeti.Contour.windingNumber_modelSector_pi` and
  `TauCeti.Contour.windingNumber_modelSector_pi_div_three` — the `½` at a smooth crossing and the
  `1/6` at a `π/3` corner, the two values the valence formula consumes.

This is Layer 1 of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3).

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — (2.4).
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- **The Hungerbühler–Wasem model sector** of radius `r` and opening angle `α` at `z₀`, with the
incoming radius at angle `φ + α` and the outgoing one at angle `φ`.

For `0 < r` and `0 ≤ α`: on `[-r, r]` it is the two-ray corner through `z₀`, running from
`z₀ + r e^{i(φ+α)}` in to `z₀` and back out to `z₀ + r e^{iφ}`; on `[r, r + α]` it is the arc of
radius `r` from angle `φ` to `φ + α`, returning to the start. For other `r`, `α` the two intervals
reverse and the branches no longer line up that way. -/
def modelSector (z₀ : ℂ) (r φ α : ℝ) : ℝ → ℂ :=
  fun t =>
    if t ≤ r then
      twoRayCorner z₀ (Complex.exp ((φ + α : ℝ) * Complex.I)) (Complex.exp ((φ : ℝ) * Complex.I)) t
    else circleMap z₀ r (φ + (t - r))

/-- Pointwise value of the model sector on the corner interval. -/
@[simp]
theorem modelSector_of_le {z₀ : ℂ} {r φ α t : ℝ} (ht : t ≤ r) :
    modelSector z₀ r φ α t =
      twoRayCorner z₀ (Complex.exp ((φ + α : ℝ) * Complex.I))
        (Complex.exp ((φ : ℝ) * Complex.I)) t := if_pos ht

/-- Pointwise value of the model sector on the arc interval. -/
@[simp]
theorem modelSector_of_lt {z₀ : ℂ} {r φ α t : ℝ} (ht : r < t) :
    modelSector z₀ r φ α t = circleMap z₀ r (φ + (t - r)) := if_neg (not_le.mpr ht)

/-- On the corner interval the model sector is its two-ray corner. -/
theorem modelSector_eqOn_corner (z₀ : ℂ) {r : ℝ} (hr : 0 < r) (φ α : ℝ) :
    EqOn (twoRayCorner z₀ (Complex.exp ((φ + α : ℝ) * Complex.I))
        (Complex.exp ((φ : ℝ) * Complex.I))) (modelSector z₀ r φ α) (uIoo (-r) r) := by
  intro t ht
  rw [Set.uIoo_of_le (by linarith), Set.mem_Ioo] at ht
  simp [modelSector, ht.2.le]

/-- On the arc interval the model sector is the reparametrised circle map. -/
theorem modelSector_eqOn_arc (z₀ : ℂ) (r φ : ℝ) {α : ℝ} (hα : 0 ≤ α) :
    EqOn (circleMap z₀ r ∘ fun t => 1 * t + (φ - r)) (modelSector z₀ r φ α) (uIoo r (r + α)) := by
  intro t ht
  rw [Set.uIoo_of_le (by linarith), Set.mem_Ioo] at ht
  have : ¬ t ≤ r := not_le.mpr ht.1
  simp only [modelSector, if_neg this, Function.comp_apply, one_mul]
  ring_nf

/-- The two ray directions of the model sector have equal (unit) length. -/
private theorem norm_modelSector_dirs (φ α : ℝ) :
    ‖Complex.exp ((φ + α : ℝ) * Complex.I)‖ = ‖Complex.exp ((φ : ℝ) * Complex.I)‖ := by
  rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]

/-- **The model sector has winding number `α / 2π` about its corner** (Hungerbühler–Wasem (2.4)).
The two radial segments contribute nothing and the arc contributes its opening angle. -/
theorem windingNumber_modelSector_eq {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (φ : ℝ) {α : ℝ} (hα : 0 ≤ α) :
    windingNumber (modelSector z₀ r φ α) (-r) (r + α) z₀ = (α : ℂ) / (2 * (Real.pi : ℂ)) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hcorner := modelSector_eqOn_corner z₀ hr φ α
  have harc := modelSector_eqOn_arc z₀ r φ hα
  have hcirc_diff : ∀ u ∈ uIcc (1 * r + (φ - r)) (1 * (r + α) + (φ - r)),
      DifferentiableAt ℝ (circleMap z₀ r) u := fun u _ => differentiable_circleMap z₀ r u
  have hcirc_deriv : ContinuousOn (deriv (circleMap z₀ r))
      (uIcc (1 * r + (φ - r)) (1 * (r + α) + (φ - r))) := by
    have hd : deriv (circleMap z₀ r) = fun θ => circleMap 0 r θ * Complex.I :=
      funext fun θ => deriv_circleMap z₀ r θ
    rw [hd]
    exact ((continuous_circleMap 0 r).mul continuous_const).continuousOn
  have hcirc_avoid : ∀ u ∈ uIcc (1 * r + (φ - r)) (1 * (r + α) + (φ - r)),
      circleMap z₀ r u ≠ z₀ := fun _ _ => circleMap_ne_center hrne
  have hpv_corner : CauchyPVExistsAt (modelSector z₀ r φ α) (-r) r (fun z => (z - z₀)⁻¹) z₀ :=
    (cauchyPVExistsAt_inv_sub_twoRayCorner (norm_modelSector_dirs φ α) r).congr_curve hcorner
  have hpv_arc : CauchyPVExistsAt (modelSector z₀ r φ α) r (r + α) (fun z => (z - z₀)⁻¹) z₀ := by
    refine CauchyPVExistsAt.congr_curve ?_ harc
    refine cauchyPVExistsAt_of_avoidance ?_ (fun t _ => circleMap_ne_center hrne) ?_
    · exact ((continuous_circleMap z₀ r).comp (by fun_prop)).continuousOn
    · have hg : Continuous (circleMap z₀ r ∘ fun t : ℝ => 1 * t + (φ - r)) :=
        (continuous_circleMap z₀ r).comp (by fun_prop)
      have hdg : deriv (circleMap z₀ r ∘ fun t : ℝ => 1 * t + (φ - r))
          = fun t => circleMap 0 r (1 * t + (φ - r)) * Complex.I := by
        funext t
        have hin : HasDerivAt (fun s : ℝ => 1 * s + (φ - r)) 1 t := by
          simpa using (_root_.HasDerivAt.const_mul (1 : ℝ) (hasDerivAt_id t)).add_const (φ - r)
        have := (hasDerivAt_circleMap z₀ r (1 * t + (φ - r))).scomp t hin
        rw [one_smul] at this
        exact this.deriv
      apply ContinuousOn.intervalIntegrable
      rw [hdg]
      refine ContinuousOn.mul (ContinuousOn.inv₀ ?_ ?_) ?_
      · exact (hg.sub continuous_const).continuousOn
      · exact fun t _ => sub_ne_zero.mpr (circleMap_ne_center hrne)
      · exact (((continuous_circleMap 0 r).comp (by fun_prop)).mul continuous_const).continuousOn
  rw [windingNumber_concat hpv_corner hpv_arc, ← windingNumber_congr_curve hcorner,
    ← windingNumber_congr_curve harc,
    windingNumber_eq_zero_twoRayCorner (norm_modelSector_dirs φ α) r,
    windingNumber_comp_mul_add hcirc_diff hcirc_deriv hcirc_avoid,
    windingNumber_circleMap_center hrne]
  push_cast
  ring

/-- **A smooth crossing contributes winding `½`** — the `α = π` model sector (HW (2.4)). This is
the coefficient of `ord_i f` in the valence formula: at the smooth boundary point `i` the contour
indents by a semicircle. -/
theorem windingNumber_modelSector_pi {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (φ : ℝ) :
    windingNumber (modelSector z₀ r φ Real.pi) (-r) (r + Real.pi) z₀ = 1 / 2 := by
  rw [windingNumber_modelSector_eq hr φ Real.pi_nonneg]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- **A `π/3` corner contributes winding `1/6`** — the `α = π/3` model sector (HW (2.4)). The two
such corners `ρ` and `ρ + 1` of the fundamental domain sum to the `1/3` coefficient of
`ord_ρ f`. -/
theorem windingNumber_modelSector_pi_div_three {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (φ : ℝ) :
    windingNumber (modelSector z₀ r φ (Real.pi / 3)) (-r) (r + Real.pi / 3) z₀ = 1 / 6 := by
  rw [windingNumber_modelSector_eq hr φ (by positivity)]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

end TauCeti.Contour

end

end
