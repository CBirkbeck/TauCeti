/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.GroupWithZero.Idempotent

/-!
# Unitality of a non-unital algebra homomorphism

A non-unital algebra homomorphism need not send `1` to `1`, and the zero map shows it need not.
Where multiplication is left-cancellative away from zero there is nothing in between: `p 1` is
idempotent, so it is `0` or `1`, and `p 1 = 0` forces `p` itself to vanish. Such a map is
therefore either the zero map or unital, with the zero map the only non-unital one; unital ones
are promoted to `AlgHom` by Mathlib's `AlgHom.ofLinearMap`.

This is the dichotomy that lets a type of multiplicative maps carry a zero without adjoining one.

## Main results

* `NonUnitalAlgHom.eq_zero_or_map_one`: a non-unital algebra map is the zero map or sends `1`
  to `1`.
* `NonUnitalAlgHom.map_one_of_ne_zero`: consequently a nonzero one is unital.
-/

public section

namespace NonUnitalAlgHom

variable {F A B : Type*} [CommSemiring F] [Semiring A] [Semiring B] [IsLeftCancelMulZero B]
  [Algebra F A] [Algebra F B]

/-- **A non-unital algebra map is the zero map or unital.** `p 1` is idempotent, hence `0` or
`1`, and at `0` the map vanishes everywhere. -/
theorem eq_zero_or_map_one (p : A →ₙₐ[F] B) : p = 0 ∨ p 1 = 1 := by
  have hidem : IsIdempotentElem (p 1) := by rw [IsIdempotentElem, ← map_mul, mul_one]
  refine (IsIdempotentElem.iff_eq_zero_or_one.mp hidem).imp (fun hz => ?_) id
  ext x
  rw [NonUnitalAlgHom.zero_apply, ← mul_one x, map_mul, hz, mul_zero]

/-- **A nonzero non-unital algebra map is unital.** -/
theorem map_one_of_ne_zero {p : A →ₙₐ[F] B} (hp : p ≠ 0) : p 1 = 1 :=
  p.eq_zero_or_map_one.resolve_left hp

end NonUnitalAlgHom

end
