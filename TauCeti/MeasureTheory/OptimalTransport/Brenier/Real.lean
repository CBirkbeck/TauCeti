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

This is the one-dimensional monotone-rearrangement check in OptimalTransport Layer 5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Gradient

namespace TauCeti

/-- For an atomless real source, the graph plan of the quantile-CDF map is the quantile coupling. -/
theorem graphPlan_quantile_cdf {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    graphPlan (fun x => ν.quantile (cdf μ x)) μ = μ.quantileCoupling ν := by
  have hmap : Measurable (fun x => (x, ν.quantile (cdf μ x))) :=
    measurable_id.prodMk (ν.measurable_quantile.comp (cdf μ).mono.measurable)
  rw [graphPlan_def]
  calc
    _ = ((volume.restrict (Ioo (0 : ℝ) 1)).map μ.quantile).map
        (fun x => (x, ν.quantile (cdf μ x))) :=
      congrArg (Measure.map (fun x => (x, ν.quantile (cdf μ x))))
        μ.map_quantile_volume_Ioo.symm
    _ = _ := by
      rw [Measure.map_map hmap μ.measurable_quantile, Measure.quantileCoupling_def]
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      simp only [Function.comp_apply, μ.cdf_quantile
        (Measure.continuous_cdf_of_noAtoms μ) hu.1 hu.2]

/-- The concrete monotone rearrangement is optimal for half the squared distance.
The source is atomless; the target may have atoms, and no moment hypothesis is needed. -/
theorem isKantorovichOptimalTransportMap_quantile_cdf
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] :
    IsKantorovichOptimalTransportMap
      (fun z : ℝ × ℝ => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      μ ν (fun x => ν.quantile (cdf μ x)) := by
  have hT : Measurable (fun x => ν.quantile (cdf μ x)) :=
    ν.measurable_quantile.comp (cdf μ).mono.measurable
  have hgraph := graphPlan_quantile_cdf (μ := μ) (ν := ν)
  have hlaw : HasLaw (fun x => ν.quantile (cdf μ x)) ν μ :=
    (isCoupling_graphPlan_iff hT.aemeasurable).1
      (hgraph ▸ μ.isCoupling_quantileCoupling ν)
  rw [isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hlaw (by fun_prop), hgraph]
  have hcost : (fun z : ℝ × ℝ => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) =
      (fun z => (1 / 2 : ℝ≥0∞) * edist z.1 z.2 ^ (2 : ℝ)) := by
    funext z
    simp only [edist_dist, Real.dist_eq, Real.norm_eq_abs, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg (z.1 - z.2))]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num [div_eq_mul_inv, mul_comm]
  rw [hcost]
  exact (μ.isOptimalCoupling_quantileCoupling ν (by norm_num : (1 : ℝ) ≤ 2)).const_mul
    (by norm_num)

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
