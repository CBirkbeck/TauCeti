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

What is *not* here is the geometric identification of each window contribution with `α_ℓ / 2π`
for the crossing angle `α_ℓ`; that is the model-sector computation
(`windingNumber_modelSector`) transported to a window of the curve, and it is what turns the sum
below into the sum of angles. The decomposition and that identification are independent, and
only the former is needed to know that the crossings are the *only* source of non-integrality.

## Main results

* `TauCeti.Contour.windingNumber_eq_windowPieceSum` — the winding number is
  `(2πi)⁻¹` times the alternating piece/window sum along the sorted crossing list.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*, Proposition 2.2.
-/

public section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- **The winding number splits into avoiding arcs and crossings** (Hungerbühler–Wasem
Proposition 2.2, aggregation half). With pairwise-disjoint windows of radius `r` about a finite
set of crossing times, interior to `[a, b]`, and with the curve staying a positive distance `m`
from `z₀` away from those windows, the generalized winding number about `z₀` is `(2πi)⁻¹` times
the alternating sum of the between-window arc values `p` and the per-window values `w`.

The arcs contribute ordinary integrals — they avoid `z₀` — so all of the non-integrality of the
winding number is carried by the finitely many window terms. -/
theorem windingNumber_eq_windowPieceSum {γ : ℝ → ℂ} {z₀ : ℂ} {p : ℝ → ℝ → ℂ} {w : ℝ → ℂ}
    {a b r m : ℝ} (hr_pos : 0 < r) (hab : a ≤ b) (crossings : Finset ℝ)
    (h_lo : ∀ t ∈ crossings, a < t - r) (h_hi : ∀ t ∈ crossings, t + r ≤ b)
    (h_pair : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|)
    (h_arc : ∀ l u : ℝ, a ≤ l → l ≤ u → u ≤ b → (∀ t ∈ Icc l u, m ≤ ‖γ t - z₀‖) →
      HasCauchyPVAt γ l u (fun z => (z - z₀)⁻¹) z₀ (p l u))
    (h_win : ∀ t ∈ crossings, HasCauchyPVAt γ (t - r) (t + r) (fun z => (z - z₀)⁻¹) z₀ (w t))
    (h_far : ∀ u ∈ Icc a b, (∀ t ∈ crossings, u ∉ Ioo (t - r) (t + r)) → m ≤ ‖γ u - z₀‖) :
    windingNumber γ a b z₀ =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        windowPieceSum r p w b (crossings.sort (· ≤ ·)) a :=
  windingNumber_eq_of_hasCauchyPVAt
    (hasCauchyPVAt_of_perWindow hr_pos hab crossings h_lo h_hi h_pair h_arc h_win h_far)

end TauCeti.Contour
