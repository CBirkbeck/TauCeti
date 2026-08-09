/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# The partial derivatives of the Weierstrass polynomial

Mathlib defines the two partial derivatives `W_X` and `W_Y` of the polynomial `W(X, Y)` of an
affine Weierstrass curve by writing them out, and records a `TODO` beside each asking for them in
terms of `Polynomial.derivative`. This file discharges that: both are `Polynomial.derivative`, in
the only two forms the types allow.

## Main results

* `TauCeti.WeierstrassCurve.Affine.derivative_polynomial`: `W_Y` is the derivative of `W(X, Y)`
  in `Y`, which is `Polynomial.derivative` on `R[X][Y]` outright.
* `TauCeti.WeierstrassCurve.Affine.derivative_eval_polynomial`: `W_X` is the derivative in `X`,
  after specialising `Y` to a constant.

The `Y`-partial is a plain `Polynomial.derivative` because `Y` is the outer variable of
`R[X][Y]`. The `X`-partial is not: differentiating the *coefficients* is not a ring homomorphism,
so there is no `Polynomial.map` to apply. Specialising `Y` to a constant `C y₀` first lands the
polynomial in `R[X]`, where `Polynomial.derivative` is the derivative in `X`. The specialisation
must be to a constant: for a non-constant `y : R[X]` the chain rule contributes a second term
`W_Y(X, y) * y'`.

Both hold over an arbitrary commutative ring, and for a Weierstrass curve that need not be
elliptic — they are identities between the defining polynomials, with no nonsingularity in sight.

This supports `TauCetiRoadmap/EllipticCurves/README.md`, Layer 0: the places-and-divisors
dictionary of the function field needs the place of an affine point, and the local ring there is a
discrete valuation ring by an argument that reads nonsingularity as a statement about
`Polynomial.derivative` of the specialised polynomial — which is what the second result supplies.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Valuation.lean`, declaration
`eval_poly_deriv_eq_polynomialX_eval`.

Changes from the source. The source states the `X`-partial over a field and keeps it `private`;
here it is public and over an arbitrary commutative ring, since nothing in it needs inverses. The
`Y`-partial has no counterpart in the source: it is the other half of Mathlib's `TODO`, and it is
the cleaner of the two, needing no specialisation at all.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace TauCeti

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve.Affine R)

/-- **The `Y`-partial derivative of the Weierstrass polynomial is its `Polynomial.derivative`.**
`Y` is the outer variable of `R[X][Y]`, so no specialisation is needed. -/
@[simp]
lemma derivative_polynomial : derivative W.polynomial = W.polynomialY := by
  simp only [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.Affine.polynomialY,
    derivative_add, derivative_sub, derivative_mul, derivative_pow, derivative_C, derivative_X,
    Nat.cast_ofNat, map_ofNat]
  ring

/-- **The `X`-partial derivative of the Weierstrass polynomial is the `Polynomial.derivative` of
its specialisation.** Fixing `Y = y` sends `W(X, Y)` into `R[X]`, where differentiating in `X`
gives `W_X(X, y)`. -/
lemma derivative_eval_polynomial (y : R) :
    derivative (W.polynomial.eval (C y)) = W.polynomialX.eval (C y) := by
  simp only [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.Affine.polynomialX, eval_add,
    eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_C, derivative_X, Nat.cast_ofNat, map_ofNat,
    C_add, C_mul, C_pow]
  ring

end WeierstrassCurve.Affine

end TauCeti

end
