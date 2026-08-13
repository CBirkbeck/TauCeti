/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Completeness of the restricted power series over a complete base

Over a complete Hausdorff uniform ring `A`, the ordinary restricted power-series ring — the
weighted ring `TauCeti.Huber.weightedRestrictedSubring` at the trivial weight family — is
itself complete and Hausdorff. At trivial weights `Tν · U = U`
(`TauCeti.Huber.weightMul_one_weight`), so the coefficient maps are uniformly continuous: a
Cauchy filter of restricted series is coefficientwise Cauchy, its coefficientwise limit is
restricted, and the filter converges to it. This is the trivial-weight case of Wedhorn's
completeness statement for `A⟨X⟩_T` (*Adic Spaces*, arXiv:1910.05934v1, 5.49); the weighted
case needs bounded weights and is not treated here.

Consequently `TauCeti.Huber.restrictedMvPowerSeriesCompletion k A` collapses for such `A`:
`UniformSpace.Completion.completeRingEquivSelf` applies to it directly through the instances
below, identifying `A⟨X₁,…,Xₖ⟩` with the plain restricted-series ring — the "comparison with
the usual completed restricted power-series algebra" milestone of roadmap Layer 0.5.

## Main results

* `TauCeti.Huber.uniformContinuous_coeff_one_weight` : at trivial weights the coefficient
  maps are uniformly continuous.
* `TauCeti.Huber.instT0Space_one_weight` : the restricted series over a Hausdorff base are
  Hausdorff.
* `TauCeti.Huber.instCompleteSpace_one_weight` : the restricted series over a complete base
  are complete.
-/

public section

namespace TauCeti.Huber

open Filter

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A]

/-- At the trivial weight family the coefficient maps of `A⟨X⟩` are uniformly continuous:
the neighbourhood subgroup `U⟨X⟩` maps into `U` coefficientwise. -/
theorem uniformContinuous_coeff_one_weight (ν : Fin k →₀ ℕ) :
    UniformContinuous fun f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) := by
  refine uniformContinuous_addMonoidHom_of_continuous (f := AddMonoidHom.mk'
    (fun f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ↦
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) fun _ _ ↦ by simp) ?_
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero,
    (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_left_iff]
  intro V hV
  obtain ⟨U, hUV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
  exact ⟨U, trivial, fun f hf ↦ hUV (by simpa using mem_weightedNhd.mp hf ν)⟩

/-- Restricted series over a Hausdorff base are Hausdorff: points are separated
coefficientwise. -/
instance instT0Space_one_weight [T0Space A] :
    T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :=
  t0Space_of_injective_of_continuous
    (f := fun f ν ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A))
    (fun _ _ h ↦ Subtype.ext (MvPowerSeries.ext fun ν ↦ congrFun h ν))
    (continuous_pi fun ν ↦ (uniformContinuous_coeff_one_weight ν).continuous)

omit [IsUniformAddGroup A] in
/-- A limit inherits a coset bound: if `u` tends to `b` and eventually stays in the coset
`c + U` of an open subgroup, then so does `b`, because an open subgroup — hence each of its
cosets — is closed. Private: a step of the completeness proof below with no weighted content. -/
private theorem sub_mem_of_tendsto {α : Type*} {l : Filter α} [l.NeBot] {u : α → A} {b c : A}
    (U : OpenAddSubgroup A) (hu : Tendsto u l (nhds b)) (h : ∀ᶠ x in l, u x - c ∈ U) :
    b - c ∈ U := by
  have hc : IsClosed ((fun y : A ↦ y - c) ⁻¹' (U : Set A)) :=
    U.isClosed.preimage (continuous_id.sub continuous_const)
  have hs : ∀ᶠ x in l, u x ∈ (fun y : A ↦ y - c) ⁻¹' (U : Set A) := h
  exact hc.closure_subset (mem_closure_of_tendsto hu hs)

omit [IsUniformAddGroup A] in
/-- A Cauchy filter on `A⟨X⟩_T` is coefficientwise uniformly Cauchy: for every open subgroup `U`
of `A` some member of the filter has all its pairwise coefficient differences inside `Tν · U`.
Private: this is the step that unfolds `U⟨X⟩` into its defining coefficient bounds, used only by
the completeness proof below. -/
private theorem exists_mem_forall_coeff_sub_mem {T : Fin k → Set A} {hT : IsWeightFamily T}
    {F : Filter (weightedRestrictedSubring T hT)} (hF : Cauchy F) (U : OpenAddSubgroup A) :
    ∃ t ∈ F, ∀ f ∈ t, ∀ g ∈ t, ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)
      - MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) A) ∈ weightMul T ν U.toAddSubgroup := by
  have hV : (weightedNhd T hT U.toAddSubgroup : Set (weightedRestrictedSubring T hT)) ∈ nhds 0 :=
    (hasBasis_nhds_zero_weightedTopology hT).mem_of_mem trivial
  have huni : (fun p : weightedRestrictedSubring T hT × weightedRestrictedSubring T hT ↦
      p.2 - p.1) ⁻¹' (weightedNhd T hT U.toAddSubgroup : Set _) ∈ uniformity _ := by
    rw [uniformity_eq_comap_nhds_zero]
    exact Filter.mem_comap.mpr ⟨_, hV, subset_rfl⟩
  obtain ⟨t, htF, ht⟩ := (cauchy_iff.mp hF).2 _ huni
  refine ⟨t, htF, fun f hf g hg ν ↦ ?_⟩
  have hfg : f - g ∈ weightedNhd T hT U.toAddSubgroup := ht (Set.mk_mem_prod hg hf)
  simpa using mem_weightedNhd.mp hfg ν

/-- **Restricted series over a complete base are complete**: a Cauchy filter is
coefficientwise Cauchy at trivial weights, its coefficientwise limit is restricted, and the
filter converges to it. -/
instance instCompleteSpace_one_weight [CompleteSpace A] :
    CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) := by
  refine ⟨fun {F} hF ↦ ?_⟩
  have : F.NeBot := hF.1
  choose a ha using fun ν ↦ CompleteSpace.complete
    (hF.map (uniformContinuous_coeff_one_weight (A := A) ν))
  obtain ⟨g, hg⟩ : ∃ g : MvPowerSeries (Fin k) A, ∀ ν, MvPowerSeries.coeff ν g = a ν :=
    ⟨a, fun _ ↦ rfl⟩
  -- Every open subgroup `U` has an `F`-set all of whose coefficients are `U`-close to `g`.
  have key : ∀ U : OpenAddSubgroup A, ∃ t ∈ F, ∀ f ∈ t, ∀ ν,
      MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) - a ν ∈ U := by
    intro U
    obtain ⟨t, htF, ht⟩ := exists_mem_forall_coeff_sub_mem hF U
    refine ⟨t, htF, fun f hf ν ↦ ?_⟩
    have h : a ν - MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ U :=
      sub_mem_of_tendsto U (ha ν)
        (Filter.eventually_of_mem htF fun f' hf' ↦ by simpa using ht f' hf' f hf ν)
    simpa using neg_mem h
  -- The coefficientwise limit is again restricted, since it is `U`-close to a restricted series.
  have hres : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) g := by
    rw [isWeightedRestricted_iff]
    intro U
    obtain ⟨t, htF, ht⟩ := key U
    obtain ⟨f₀, hf₀⟩ := hF.1.nonempty_of_mem htF
    filter_upwards [isWeightedRestricted_iff.mp (mem_weightedRestrictedSubring.mp f₀.2) U] with ν hν
    have h₀ : MvPowerSeries.coeff ν (f₀ : MvPowerSeries (Fin k) A) ∈ U := by simpa using hν
    simpa [hg] using sub_mem h₀ (ht f₀ hf₀ ν)
  refine ⟨⟨g, mem_weightedRestrictedSubring.mpr hres⟩, ?_⟩
  rw [← tendsto_id', ← tendsto_sub_nhds_zero_iff,
    (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_right_iff]
  intro U _
  obtain ⟨t, htF, ht⟩ := key U
  filter_upwards [htF] with f hf
  rw [SetLike.mem_coe, mem_weightedNhd]
  intro ν
  simpa [map_sub, hg] using ht f hf ν

end TauCeti.Huber
