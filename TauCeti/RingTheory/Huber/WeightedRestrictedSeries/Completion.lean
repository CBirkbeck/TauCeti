/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic
public import Mathlib.Topology.Algebra.UniformRing

/-!
# The completed restricted power-series algebra `A⟨X₁,…,Xₖ⟩`

For a nonarchimedean commutative ring `A`, the separated completion of the ring of restricted
power series in `k` variables — the weighted ring `TauCeti.Huber.weightedRestrictedSubring`
at the trivial weight family `Tᵢ = {1}` (Wedhorn *Adic Spaces*, arXiv:1910.05934v1, Example
5.54). `A` is not assumed complete or Hausdorff; for `k = 0` the construction is the separated
completion of `A` itself.

Being a completion, `A⟨X₁,…,Xₖ⟩` is a complete Hausdorff topological `A`-algebra with all of
that structure found by instance search, which is why this module is short: it fixes the
notation and records the one fact instance search does not supply, continuity of the structure
map.

The predicate that every `A⟨X₁,…,Xₖ⟩` is noetherian is
`TauCeti.Huber.IsStronglyNoetherian`, in `TauCeti.RingTheory.Huber.StronglyNoetherian`; the
comparison with the plain restricted-series ring over a complete Hausdorff base is
`TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv`, in
`TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete`.

## Main definitions

* `TauCeti.Huber.restrictedMvPowerSeriesCompletion`: the completed restricted power-series
  algebra `A⟨X₁,…,Xₖ⟩`.

## Main results

* `TauCeti.Huber.continuous_algebraMap_restrictedMvPowerSeriesCompletion`: the structure map
  `A → A⟨X₁,…,Xₖ⟩` is continuous.
-/

public section

namespace TauCeti.Huber

variable (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- The completed restricted power-series algebra `A⟨X₁,…,Xₖ⟩` of a nonarchimedean commutative
ring `A`: the separated completion of the ring of restricted power series in `k` variables —
the weighted ring `TauCeti.Huber.weightedRestrictedSubring` at the trivial weight family
`Tᵢ = {1}` — with respect to the uniformity of its ring topology. For `k = 0` this is the
separated completion of `A` itself. -/
noncomputable abbrev restrictedMvPowerSeriesCompletion : Type _ :=
  UniformSpace.Completion
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)

/-- The structure map `A → A⟨X₁,…,Xₖ⟩` is continuous. -/
theorem continuous_algebraMap_restrictedMvPowerSeriesCompletion :
    Continuous (algebraMap A (restrictedMvPowerSeriesCompletion k A)) := by
  have h : Continuous (algebraMap A (weightedRestrictedSubring
      (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)) :=
    (continuous_weightedC isWeightFamily_one_weight).congr fun a ↦ Subtype.ext (by simp)
  exact ((UniformSpace.Completion.continuous_coe _).comp h).congr fun a ↦
    (UniformSpace.Completion.algebraMap_def _ _ a).symm

end TauCeti.Huber
