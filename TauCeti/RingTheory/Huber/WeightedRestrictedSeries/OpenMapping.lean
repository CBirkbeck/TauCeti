/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.OpenMapping
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

/-!
# The weight condition from openness, via the open mapping theorem

`TauCeti.Huber.IsWeightFamily` asks that `Tᵢ^m · U` be a neighbourhood of `0` for every
neighbourhood `U` — that multiplication by a weight is an open *map*. The roadmap instead phrases
the condition as each `Tᵢ · A` being *open*, and `IsWeightFamily.of_exists_isOpenMap_mul`'s
docstring records that the two coincide only under an open mapping theorem.

Over a complete Tate ring that theorem is available, as
`TauCeti.Huber.IsTateRing.isOpenMap`, so this file closes the gap.

It is a separate file rather than an addition to `WeightedRestrictedSeries.Basic` on import
weight: importing `Huber.OpenMapping` there would take that file's closure from 17 modules to 40,
pulling Baire category theory and the whole Henkel stack into the file that merely *defines*
`IsWeightFamily`.

## Main results

* `TauCeti.Huber.IsWeightFamily.of_isOpen_span`: a family whose weights each contain an element
  generating an open ideal is a weight family.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Theorem 6.16 for the open
  mapping theorem this consumes.
-/

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsTateRing A] [CompleteSpace A] [T0Space A]

/-- **The roadmap's phrasing of the weight condition.** If each `Tᵢ` contains a `t` whose
principal ideal is open, the family is a weight family.

This is `TauCeti.Huber.IsWeightFamily.of_exists_isOpenMap_mul` fed by
`TauCeti.Huber.isOpenMap_mul_of_isOpen_span`; the completeness and Tate hypotheses are what that
open mapping theorem needs, and are not used elsewhere. -/
theorem IsWeightFamily.of_isOpen_span {k : ℕ} {T : Fin k → Set A}
    (h : ∀ i, ∃ t ∈ T i, IsOpen ((Ideal.span {t} : Ideal A) : Set A)) : IsWeightFamily T :=
  IsWeightFamily.of_exists_isOpenMap_mul fun i ↦
    (h i).imp fun _ ht ↦ ⟨ht.1, isOpenMap_mul_of_isOpen_span ht.2⟩

end TauCeti.Huber

end
