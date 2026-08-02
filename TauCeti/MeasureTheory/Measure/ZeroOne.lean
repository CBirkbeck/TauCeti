/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

/-!
# Zero-one laws are almost surely constant

A zero-one measure gives every measurable set mass `0` or `1`. Mathlib's
`MeasureTheory.IsZeroOneMeasure.exists_eq_dirac` identifies such a measure with a Dirac mass, but
only when the carrier is standard Borel. This file records the form that survives on an arbitrary
carrier: a measurable map *into* a standard Borel space is almost surely constant, because its
pushforward is again a zero-one probability measure and is therefore Dirac.

That is the form a carrier without a standard Borel structure of its own needs, since such a space
can still be embedded measurably into one and the conclusion pulled back along the embedding.

## Main results

* `TauCeti.MeasureTheory.exists_ae_eq_const_of_isZeroOneMeasure`: under a zero-one measure, a
  measurable map into a standard Borel space agrees almost everywhere with a single value.
-/

public section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

/-- **A zero-one law is almost surely constant along a measurable map.** The pushforward of a
zero-one probability measure along `f` is again a zero-one probability measure; on a standard Borel
space it is therefore a Dirac mass at some `q`, and the fibre `f ⁻¹' {q}` has full measure.

Only the measurability of `f` is required: the carrier `Ω` needs no topological or Borel structure,
which is the point of the statement. -/
theorem exists_ae_eq_const_of_isZeroOneMeasure {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [StandardBorelSpace β] {π : Measure Ω} [IsProbabilityMeasure π]
    [IsZeroOneMeasure π] {f : Ω → β} (hf : Measurable f) :
    ∃ q : β, ∀ᵐ ω ∂π, f ω = q := by
  haveI : IsProbabilityMeasure (π.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  haveI : IsZeroOneMeasure (π.map f) := {
    zero_one₀ := fun s hs => by
      rw [Measure.map_apply hf hs]
      exact _root_.MeasureTheory.Measure.zero_one π (f ⁻¹' s) }
  obtain ⟨q, hq⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := π.map f)
  have hsingleton : MeasurableSet ({q} : Set β) := MeasurableSet.singleton q
  have hmass : π (f ⁻¹' {q}) = 1 := by
    rw [← Measure.map_apply hf hsingleton, hq]
    simp
  exact ⟨q, (_root_.MeasureTheory.mem_ae_iff_prob_eq_one (hsingleton.preimage hf)).2 hmass⟩

end MeasureTheory

end TauCeti
