/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# The Weierstrass partial derivatives are derivatives

Mathlib defines the two partial derivatives `WeierstrassCurve.Affine.polynomialX` and
`WeierstrassCurve.Affine.polynomialY` of the Weierstrass polynomial `W(X, Y)` by explicit
formulae, and marks both definitions with the comment
`TODO: define this in terms of Polynomial.derivative`. This file identifies each of them with the
derivative it is named after.

## Main statements

* `WeierstrassCurve.Affine.derivative_polynomial`: `W_Y` is `Polynomial.derivative W(X, Y)`, an
  identity of bivariate polynomials. No evaluation is involved: `R[X][Y]` is a polynomial ring in
  `Y` over `R[X]`, so `Polynomial.derivative` already differentiates in `Y`.
* `WeierstrassCurve.Affine.derivative_eval_polynomial`: the chain rule along a substitution
  `Y := p`, which expresses `derivative (W(X, p))` through *both* partials. For a constant
  `p = C y` the `Y`-term drops out and this reads `W_X(X, y)`.

Both hold over an arbitrary commutative ring.

## Implementation notes

`Polynomial.derivative` on `R[X][Y]` differentiates in `Y`, so `derivative_polynomial` is an
identity of bivariate polynomials with no evaluation anywhere. Differentiating in `X` instead means
differentiating the coefficients, and that *is* expressible bare, as
`PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs W.polynomial)` — the shape
standing on the right of `Polynomial.Bivariate.pderiv_zero_equivMvPolynomial`; no `MvPolynomial`
transport is needed to say it.

`derivative_eval_polynomial` is nonetheless stated after substituting `Y := p`, for two reasons
that are about usability rather than expressibility: that is the form consumers meet the partials
in, and it avoids a round trip through `PolynomialModule`. At that level the two partials appear
together, as the chain rule, rather than one at a time.

## Provenance

Both statements were extracted from the proof of
`WeierstrassCurve.Affine.Point.nonsingular_of_isUnit_XYIdeal` in `Affine/Point/ToClass.lean`,
which is itself ported from the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, by Chris Birkbeck). There they were local `have`s
over a field, and stated after evaluating at a point; here they are stated over a commutative
ring, and before evaluation.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W : Affine R}

/-- **The `Y`-partial derivative of `W(X, Y)` is a `Polynomial.derivative`.** Viewing `R[X][Y]` as
a polynomial ring in `Y` over `R[X]`, differentiating `W(X, Y)` in `Y` gives `W_Y(X, Y)` on the
nose. -/
@[simp] theorem derivative_polynomial : derivative W.polynomial = W.polynomialY := by
  simp only [polynomial, polynomialY, derivative_sub, derivative_add, derivative_mul,
    derivative_C, derivative_X_pow, derivative_X, C_ofNat, Nat.cast_ofNat, zero_mul, zero_add,
    sub_zero, mul_one, pow_one, Nat.add_one_sub_one]

/-- **The chain rule for `W(X, Y)` along a substitution `Y := p`.** Differentiating the
one-variable polynomial `W(X, p)` splits into the two partials of `W`, the `Y`-one weighted by
`p'`. Substituting a constant `p = C y` kills the second term and leaves `W_X(X, y)`. -/
@[simp] theorem derivative_eval_polynomial (p : R[X]) :
    derivative (W.polynomial.eval p) =
      W.polynomialX.eval p + W.polynomialY.eval p * derivative p := by
  simp only [polynomial, polynomialX, polynomialY, C_add, C_mul, C_pow, eval_sub, eval_add,
    eval_pow, eval_X, eval_mul, eval_C, eval_ofNat, derivative_sub, derivative_add, derivative_mul,
    derivative_C, derivative_pow, derivative_X, C_ofNat, Nat.cast_ofNat, zero_mul, add_zero,
    zero_add, mul_one, pow_one, Nat.add_one_sub_one]
  ring

end WeierstrassCurve.Affine

end
