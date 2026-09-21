/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Algebra.Module.ZLattice.Basic

/-!
# A fundamental domain of the shape a counting argument consumes

`ZSpan.fundamentalDomain` is attached to a choice of basis, and its properties are spread over
several Mathlib declarations, each stated in its own idiom: tiling appears as
`ZSpan.exist_unique_vadd_mem_fundamentalDomain` in `+ᵥ` form, while a counting argument wants it
as existence and uniqueness of the lattice vector `w` with `x - w ∈ F`.

`TauCeti.exists_fundamentalDomain` packages a single choice of domain with every property such an
argument needs, so that a consumer neither picks a basis nor converts between the two idioms.

## Main results

* `TauCeti.exists_fundamentalDomain`: a `ZLattice` admits a bounded measurable preconnected
  fundamental domain containing `0`, tiling the space in subtraction form, whose measure is the
  covolume.
-/

public section

open Bornology MeasureTheory Module Set Submodule

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **A fundamental domain with everything a lattice-point count asks of it.** For a `ZLattice`
`L` there is a set `F` that contains `0`, is preconnected, bounded and measurable, meets each
orbit `x - L` exactly once, and has `μ.real F = ZLattice.covolume L μ`.

Preconnectedness is what makes a cell straddling a set meet its frontier; boundedness and
measurability are what let the cells be counted; and the measure identity is what turns a count of
cells into a volume. -/
theorem exists_fundamentalDomain :
    ∃ F : Set E, (0 : E) ∈ F ∧ IsPreconnected F ∧ IsBounded F ∧ MeasurableSet F ∧
      (∀ x : E, ∀ w₁ ∈ (L : Set E), ∀ w₂ ∈ (L : Set E), x - w₁ ∈ F → x - w₂ ∈ F → w₁ = w₂) ∧
      (∀ x : E, ∃ w ∈ (L : Set E), x - w ∈ F) ∧ ZLattice.covolume L μ = μ.real F := by
  classical
  set b := Module.Free.chooseBasis ℤ L
  set β := b.ofZLatticeBasis ℝ L
  have hmem : ∀ w : E, w ∈ (L : Set E) ↔ w ∈ span ℤ (Set.range β) := fun w ↦ by
    rw [b.ofZLatticeBasis_span ℝ]
    exact Iff.rfl
  exact ⟨ZSpan.fundamentalDomain β, by simp [ZSpan.mem_fundamentalDomain],
    (ZSpan.convex_fundamentalDomain β).isPreconnected, ZSpan.fundamentalDomain_isBounded β,
    ZSpan.fundamentalDomain_measurableSet β,
    fun _ w₁ h₁ w₂ h₂ k₁ k₂ ↦ ZSpan.eq_of_sub_mem_fundamentalDomain β ((hmem w₁).mp h₁)
      ((hmem w₂).mp h₂) k₁ k₂,
    fun x ↦ ⟨(ZSpan.floor β x : E), (hmem _).mpr (ZSpan.floor β x).2,
      ZSpan.fract_mem_fundamentalDomain β x⟩,
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)⟩

end TauCeti
