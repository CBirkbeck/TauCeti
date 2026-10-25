/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Rearrangement

/-!
# The monotone rearrangement is a Brenier map

For an atomless real source law, the map `x ↦ ν.quantile (cdf μ x)` has graph plan equal to the
native common-uniform quantile coupling. It is therefore optimal for the half-squared distance.
For an absolutely continuous source and finite optimal cost, Brenier's map uniqueness identifies
this concrete map almost everywhere with the gradient of a convex potential, retaining the
potential's finiteness and differentiability conditions.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Gradient

namespace TauCeti

/-- For an absolutely continuous real source and finite quadratic optimal cost, the concrete
quantile-CDF rearrangement is almost everywhere the gradient of a convex potential. The potential
is finite near almost every source point and its real representative is differentiable there. -/
theorem exists_convex_gradient_quantile_cdf
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ volume)
    (hfin : transportCost
      (fun z : ℝ × ℝ => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞) :
    ∃ u : ℝ → EReal, Convex ℝ {p : ℝ × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧
        DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      (fun x => ν.quantile (cdf μ x)) =ᵐ[μ] ∇ fun x => (u x).toReal := by
  have : NullSingletonClass μ := ⟨fun x => hμ (measure_singleton x)⟩
  obtain ⟨u, hconv, hlsc, hbot, hdiff, _, _, huniq⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient hμ hfin
  exact ⟨u, hconv, hlsc, hbot, hdiff, huniq _ isKantorovichOptimalTransportMap_quantile_cdf⟩

end TauCeti
