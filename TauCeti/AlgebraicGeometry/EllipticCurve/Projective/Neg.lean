/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# Negation of solutions of the projective Weierstrass equation

For a Weierstrass curve `W'` over a commutative ring, Mathlib's negation
`WeierstrassCurve.Projective.neg` sends a point representative `[P₀ : P₁ : P₂]` to
`[P₀ : -P₁ - a₁P₀ - a₃P₂ : P₂]`. Mathlib shows that it preserves nonsingularity over a field; this
file shows that over any commutative ring it preserves the projective Weierstrass equation.

## Main results

* `WeierstrassCurve.Projective.equation_neg`: the negation of a point representative is a solution
  of the projective Weierstrass equation exactly when the representative is.
-/

public section

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] {W' : Projective R}

/-- The negation `W'.neg P = [P₀ : -P₁ - a₁P₀ - a₃P₂ : P₂]` of a point representative `P` is a
solution of the projective Weierstrass equation exactly when `P` is: the projective form of
`WeierstrassCurve.Affine.equation_neg`. -/
theorem equation_neg (P : Fin 3 → R) : W'.Equation (W'.neg P) ↔ W'.Equation P := by
  rw [equation_iff, equation_iff, neg_X, neg_Y, neg_Z, negY]
  congr! 1
  ring1

end WeierstrassCurve.Projective
