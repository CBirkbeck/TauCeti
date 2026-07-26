/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Circle
public import TauCeti.Analysis.Contour.Winding.Number.Concat
public import TauCeti.Analysis.Contour.Winding.Number.Reparam
public import TauCeti.Analysis.Contour.Winding.Number.Segment

/-!
# The half-disc boundary contour

The boundary of the upper half-disc of radius `R` about the origin, traversed counterclockwise:
the diameter along the real axis from `-R` to `R`, followed by the semicircular arc back to `-R`.
Parametrized on `[-R, R + π]`, with the arc carrying its angle in `t - R`.

Its distinguishing feature is that it passes **through** the origin rather than indenting around
it, so the origin is an on-curve point and the generalized winding number there is the
smooth-crossing value `½` rather than `0` or `1`:

* the diameter contributes `0` — the index integrand `1 / t` is odd, so its principal value over
  the symmetric interval vanishes (`windingNumber_eq_zero_segment`);
* the arc contributes `½` — it is a semicircle about its own centre
  (`windingNumber_circleMap_center_eq_half`).

That `½` is exactly the hypothesis of the Hungerbühler–Wasem half-residue theorem
`hasCauchyPV_half_residue`, which is why this contour is the one HW's motivating example uses: a
Cauchy principal value along the real axis with a simple pole at the origin, where the classical
residue theorem does not apply because the pole lies *on* the contour.

## Main results

* `TauCeti.Contour.halfDiscBoundary` — the contour.
* `TauCeti.Contour.windingNumber_halfDiscBoundary` — its generalized winding number about the
  origin is `½`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Thm 3.3.
-/

public section

noncomputable section

open Complex Set

namespace TauCeti.Contour

variable {R : ℝ}

/-- **The half-disc boundary contour.** On `[-R, R + π]`: the diameter `t ↦ t` for `t ≤ R`,
then the semicircular arc `t ↦ R e^{i(t-R)}` from `R` back to `-R`. -/
@[expose] def halfDiscBoundary (R : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ R then (t : ℂ) else circleMap 0 R (t - R)

/-- On the interior of the diameter's parameter interval the contour is the real segment. -/
theorem eqOn_halfDiscBoundary_segment (hR : 0 < R) :
    EqOn (fun t : ℝ => (1 : ℂ) * (t : ℂ) + 0) (halfDiscBoundary R) (uIoo (-R) R) := by
  intro t ht
  have h2 : t < max (-R) R := (Set.mem_Ioo.mp ht).2
  rw [max_eq_right (by linarith : (-R : ℝ) ≤ R)] at h2
  simp [halfDiscBoundary, h2.le]

/-- On the interior of the arc's parameter interval the contour is the reparametrized circle. -/
theorem eqOn_halfDiscBoundary_arc (R : ℝ) :
    EqOn (circleMap 0 R ∘ fun t : ℝ => 1 * t + (-R)) (halfDiscBoundary R)
      (uIoo R (R + Real.pi)) := by
  intro t ht
  have h1 : min R (R + Real.pi) < t := (Set.mem_Ioo.mp ht).1
  rw [min_eq_left (by linarith [Real.pi_pos] : R ≤ R + Real.pi)] at h1
  simp [halfDiscBoundary, not_le.mpr h1, sub_eq_add_neg]

end TauCeti.Contour

end

end
