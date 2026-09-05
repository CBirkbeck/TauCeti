/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.Algebra.GroupWithZero.Idempotent

/-!
# Unitality of a multiplicative map

A map that preserves multiplication and zero need not preserve `1`, and the zero map shows it
need not. Where multiplication in the codomain is left-cancellative away from zero there is
nothing in between: `p 1` is idempotent, so it is `0` or `1`, and `p 1 = 0` forces `p` to vanish
everywhere. Such a map is therefore either identically zero or unital, the zero map being the
only non-unital one; a unital one is promoted by `AlgHom.ofLinearMap` or `RingHom.mk'`.

This is the dichotomy that lets a type of multiplicative maps carry a zero without adjoining one.

## Main results

* `NonUnitalRingHomClass.forall_apply_eq_zero_or_map_one`: such a map vanishes identically or
  sends `1` to `1`.

## Implementation notes

Stated for `NonUnitalRingHomClass` rather than for a bundled `NonUnitalRingHom` or
`NonUnitalAlgHom`: the proof uses only `map_mul`, so any bundled type in that class gets the
result with no specialisation to restate. The conclusion is the pointwise `∀ x, p x = 0` because
the class does not provide a `Zero` on the map type itself; a bundled consumer combines it with
extensionality.
-/

public section

variable {A B G : Type*} [NonAssocSemiring A] [Semiring B] [IsLeftCancelMulZero B]
  [FunLike G A B]
  [NonUnitalRingHomClass G A B]

namespace NonUnitalRingHomClass

/-- **A multiplicative map vanishes identically or is unital.** `p 1` is idempotent, hence `0`
or `1`, and at `0` the map kills every `x = x * 1`. -/
theorem forall_apply_eq_zero_or_map_one (p : G) : (∀ x, p x = 0) ∨ p 1 = 1 := by
  have hidem : IsIdempotentElem (p 1) := by rw [IsIdempotentElem, ← map_mul, mul_one]
  refine (IsIdempotentElem.iff_eq_zero_or_one.mp hidem).imp (fun hz x => ?_) id
  rw [← mul_one x, map_mul, hz, mul_zero]

/-- **A multiplicative map that is somewhere nonzero is unital.** -/
theorem map_one_of_exists_apply_ne_zero {p : G} (hp : ∃ x, p x ≠ 0) : p 1 = 1 :=
  (forall_apply_eq_zero_or_map_one p).resolve_left fun h => by
    obtain ⟨x, hx⟩ := hp
    exact hx (h x)

end NonUnitalRingHomClass

end
