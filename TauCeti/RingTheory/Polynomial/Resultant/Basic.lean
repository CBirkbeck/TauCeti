/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The resultant against a reversed linear factor

Mathlib evaluates the resultant against a power of `X - C x`
(`Polynomial.resultant_X_sub_C_pow_right`). This file records the companion for the *reversed*
linear polynomial `C x - X`, which is the shape that arises as `x - θ` in `AdjoinRoot f`: the
answer is `f.eval x`, with **no sign**. The absence of a sign is the point — `C x - X` is
`-(X - C x)`, which contributes `(-1) ^ m`, and `resultant_X_sub_C_pow_right` contributes another
`(-1) ^ m`, so the two cancel.

## Main results

* `Polynomial.resultant_C_sub_X`

## Provenance

Adapted from Michael Stoll's `EllipticCurves`
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/Mathlib/Basic.lean` line 615, where
it is a Mathlib-bound prerequisite of the explicit `2`-descent.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The resultant of `f` with the linear polynomial `C x - X` is `f.eval x`. Note the absence of
a sign: `C x - X` is `-(X - C x)`, and the two signs cancel. -/
theorem resultant_C_sub_X (f : R[X]) (x : R) (m : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  have h : f.resultant (X - C x) m 1 = (-1) ^ m * f.eval x := by
    have := resultant_X_sub_C_pow_right f x m 1 hm
    rwa [pow_one, mul_one, pow_one] at this
  -- `C x - X` is `X - C x` scaled by the constant `-1`
  have hneg : C x - X = C (-1 : R) * (X - C x) := by simp
  rw [hneg, resultant_C_mul_right, h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, one_mul]

end Polynomial
