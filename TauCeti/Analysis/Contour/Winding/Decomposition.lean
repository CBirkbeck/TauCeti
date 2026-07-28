/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Crossing.PVAggregation
public import TauCeti.Analysis.Contour.Winding.Number.Basic

/-!
# The winding-number decomposition at a finite crossing set

Hungerbühler–Wasem Proposition 2.2 splits the generalized winding number of a curve about a
point it meets into a part coming from the arcs that avoid the point and a part coming from the
crossings themselves:

`n_{z₀}(Λ) = n_{z₀}(Λ̃) + Σ_ℓ α_ℓ / 2π`.

The proposition has two halves. The finiteness of the crossing set is
`TauCeti.Contour.IsPwC1ImmersionOn.finite_crossings`. This file is the other half: given
pairwise-disjoint windows about the crossings, the winding number is the alternating sum of the
avoiding-arc contributions and the per-window contributions.

Two things are deliberately *not* here. The crossing set is passed in rather than identified
with `{t | γ t = z₀}` — `IsPwC1ImmersionOn.finite_crossings` supplies that finiteness, but a
caller may also want a coarser set. And the per-window values `w` are still hypotheses: turning
each into the model-sector value `α_ℓ / 2π` for the crossing angle `α_ℓ` is the geometric half of
the proposition, and is independent of the aggregation done here. Only the aggregation is needed
to know that the crossings are the *only* source of non-integrality.

## Main results

* `TauCeti.Contour.windingNumber_eq_windowPieceSum` — the winding number is
  `(2πi)⁻¹` times the alternating piece/window sum along the sorted crossing list.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Proposition 2.2.
-/

public section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- **The winding number splits into avoiding arcs and crossings** (Hungerbühler–Wasem
Proposition 2.2, aggregation half). With pairwise-disjoint windows of radius `r` about a finite
set of crossing times, interior to `[a, b]`, and the curve staying a distance `≥ m > 0` from `z₀`
away from those windows, the generalized winding number about `z₀` is `(2πi)⁻¹` times the
alternating sum of the arc integrals and the per-window values.

The arcs are *ordinary* integrals, not principal values: off the windows the curve is bounded
away from `z₀`, so the truncation is eventually inactive there. All of the non-integrality of the
winding number is therefore carried by the finitely many window terms. -/
theorem windingNumber_eq_windowPieceSum {γ : ℝ → ℂ} {z₀ : ℂ} {w : ℝ → ℂ}
    {a b r m : ℝ} (hr_pos : 0 < r) (hab : a ≤ b) (hm_pos : 0 < m) (crossings : Finset ℝ)
    (h_lo : ∀ t ∈ crossings, a < t - r) (h_hi : ∀ t ∈ crossings, t + r ≤ b)
    (h_pair : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|)
    (h_int_tr : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable (fun t => if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0)
        MeasureTheory.volume a b)
    (h_win : ∀ t ∈ crossings, HasCauchyPVAt γ (t - r) (t + r) (fun z => (z - z₀)⁻¹) z₀ (w t))
    (h_far : ∀ u ∈ Icc a b, (∀ t ∈ crossings, u ∉ Ioo (t - r) (t + r)) → m ≤ ‖γ u - z₀‖) :
    windingNumber γ a b z₀ =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        windowPieceSum r (fun l u => ∫ t in l..u, (γ t - z₀)⁻¹ * deriv γ t) w b
          (crossings.sort (· ≤ ·)) a :=
  windingNumber_eq_of_hasCauchyPVAt
    (hasCauchyPVAt_of_perWindow hr_pos hab crossings h_lo h_hi h_pair
      (fun l u hA hlu hu h_far' =>
        hasCauchyPVAt_of_dist_lower_bound hlu hm_pos h_far' fun ε hε =>
          (h_int_tr ε hε).mono_set (by
            rw [uIcc_of_le hlu, uIcc_of_le hab]; exact Icc_subset_Icc hA hu))
      h_win h_far)

end TauCeti.Contour
