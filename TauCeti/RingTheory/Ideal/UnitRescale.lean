/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Rescaling a generating set by a unit

Multiplying every generator of an ideal by one fixed unit does not change the ideal. This is
elementary, but it is not in Mathlib in this form and it is what makes a *presentation* of a
rational subset rescalable: the condition that the numerators together with the denominator
generate the unit ideal survives replacing `(T, s)` by `(u · T, u · s)`.

## Main results

* `Ideal.span_image_mul_left_of_isUnit`: `span (u * ·) '' S = span S` for a unit `u`.
* `Ideal.span_insert_mul_left_of_isUnit`: the same with a distinguished generator carried along,
  which is the shape a rational-subset condition has.

## Implementation notes

Both are stated for a `Set`, not a `Finset`, although the presentations that motivate them carry
a `Finset` of numerators. `Finset.image` needs `DecidableEq`, which the ambient ring of a
presentation has no reason to carry; a consumer holding a `Finset T` reaches these through
`Finset.coe_image` and pays that cost only where it already has the instance.
-/

public section

namespace Ideal

variable {R : Type*} [CommSemiring R] {u : R}

/-- **Scaling every generator by a unit does not change the ideal they span.** -/
theorem span_image_mul_left_of_isUnit (hu : IsUnit u) (S : Set R) :
    span ((u * ·) '' S) = span S := by
  obtain ⟨v, rfl⟩ := hu
  refine le_antisymm (span_le.mpr ?_) (span_le.mpr fun x hx ↦ ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact mul_mem_left _ _ (subset_span hx)
  · have hmem : (v : R) * x ∈ span ((fun y ↦ (v : R) * y) '' S) := subset_span ⟨x, hx, rfl⟩
    simpa using mul_mem_left _ ((v⁻¹ : Rˣ) : R) hmem

/-- The rescaling of a presentation `(T, s)`: scaling the distinguished generator and all the
others by one unit leaves the ideal alone. Rewriting along this transports a rational-subset
condition `span (insert s T) = ⊤` to the rescaled presentation. -/
theorem span_insert_mul_left_of_isUnit (hu : IsUnit u) (s : R) (S : Set R) :
    span (insert (u * s) ((u * ·) '' S)) = span (insert s S) := by
  rw [← Set.image_insert_eq, span_image_mul_left_of_isUnit hu]

end Ideal

end
