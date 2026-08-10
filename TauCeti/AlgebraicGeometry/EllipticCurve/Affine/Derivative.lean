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
* `TauCeti.WeierstrassCurve.Affine.equivPolynomial_mapCoeffs_polynomial`: `W_X` is the
  *coefficient-wise* derivative, Mathlib's `Derivation.mapCoeffs` applied to
  `Polynomial.derivative'`, read back as a bivariate polynomial; and
  `eval_mapCoeffs_polynomial` is its evaluated form.
* `TauCeti.WeierstrassCurve.Affine.derivative_eval_polynomial`: the chain rule — substituting a
  polynomial `y : R[X]` for `Y` and differentiating in `X` gives `W_X(X, y) + W_Y(X, y) · y'`.
* `TauCeti.WeierstrassCurve.Affine.derivative_eval_polynomial_C`: the constant case `y' = 0`,
  where the derivative is `W_X` alone.

The `Y`-partial is a plain `Polynomial.derivative` because `Y` is the outer variable of
`R[X][Y]`. The `X`-partial is not: differentiating the *coefficients* is not a ring homomorphism,
so there is no `Polynomial.map` to apply — it is a *derivation*, and Mathlib's
`Derivation.mapCoeffs` is the one that lifts `Polynomial.derivative` coefficient-wise. The chain
rule then costs nothing: it is Mathlib's `Derivation.apply_eval_eq` with the two partials
identified, `W_X` alone only when the substituted polynomial is constant.

All of them hold over an arbitrary commutative ring, and for a Weierstrass curve that need not be
elliptic — they are identities between the defining polynomials, with no nonsingularity in sight.

This supports `TauCetiRoadmap/EllipticCurves/README.md`, Layer 0: the places-and-divisors
dictionary of the function field needs the place of an affine point, and the local ring there is a
discrete valuation ring by an argument that reads nonsingularity as a statement about
`Polynomial.derivative` of the polynomial specialised at that point — which is what
`derivative_eval_polynomial_C` supplies.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Valuation.lean`, declaration
`eval_poly_deriv_eq_polynomialX_eval`.

Changes from the source. The source states the `X`-partial over a field, only at a constant, and
keeps it `private` — it is an internal step of its DVR proof. Here it is public, over an arbitrary
commutative ring since nothing in it needs inverses, and stated as the chain rule for an arbitrary
substituted polynomial, of which the source's statement is the `y' = 0` case. Neither the
`Y`-partial nor the coefficient-wise reading of the `X`-partial has a counterpart in the source:
they are the two halves of Mathlib's `TODO`, and between them the chain rule is Mathlib's own
`Derivation.apply_eval_eq` rather than a fresh computation.
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
  simp [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.Affine.polynomialY, map_ofNat,
    derivative_pow, Nat.cast_ofNat]

private lemma equivPolynomialSelf_mapCoeffs_polynomial :
    PolynomialModule.equivPolynomialSelf ((derivative' (R := R)).mapCoeffs W.polynomial)
      = W.polynomialX := by
  -- Transport to `MvPolynomial (Fin 2) R`, where Mathlib's `pderiv_zero_equivMvPolynomial`
  -- already identifies this construction with `pderiv 0`, and compute there.
  apply (Polynomial.Bivariate.equivMvPolynomial R).injective
  rw [← Polynomial.Bivariate.pderiv_zero_equivMvPolynomial]
  simp [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.Affine.polynomialX, map_ofNat]
  ring

/-- **The `X`-partial derivative of the Weierstrass polynomial is its coefficient-wise
derivative.** Differentiating the coefficients of a polynomial in `R[X][Y]` is Mathlib's
`Derivation.mapCoeffs` applied to `Polynomial.derivative'`; read back as a bivariate polynomial,
it is `W_X`. This is the pairing of `derivative_polynomial`: Mathlib's
`pderiv_zero_equivMvPolynomial` and `pderiv_one_equivMvPolynomial` identify these two
constructions with the two partial derivatives of the corresponding `MvPolynomial`. -/
@[simp]
lemma equivPolynomial_mapCoeffs_polynomial :
    PolynomialModule.equivPolynomial ((derivative' (R := R)).mapCoeffs W.polynomial)
      = W.polynomialX :=
  -- `equivPolynomialSelf` is `equivPolynomial` by definition. The statement takes the latter,
  -- which is the simp-normal side; the computation above needs the former, which is the
  -- `R[X][Y]`-linear one.
  equivPolynomialSelf_mapCoeffs_polynomial W

/-- **The `X`-partial derivative, evaluated.** `W_X(X, y)` is the value at `y` of the
coefficient-wise derivative of `W(X, Y)`. -/
@[simp]
lemma eval_mapCoeffs_polynomial (y : R[X]) :
    PolynomialModule.eval y ((derivative' (R := R)).mapCoeffs W.polynomial)
      = W.polynomialX.eval y := by
  -- Mathlib's `aeval_equivPolynomial` at `S = R = R[X]` is the bridge from `PolynomialModule.eval`
  -- to evaluating the corresponding polynomial.
  have h := PolynomialModule.aeval_equivPolynomial (S := R[X]) (R := R[X])
    ((derivative' (R := R)).mapCoeffs W.polynomial) y
  rw [Polynomial.coe_aeval_eq_eval] at h
  simpa [equivPolynomial_mapCoeffs_polynomial] using h.symm

/-- **The chain rule for the Weierstrass polynomial.** Substituting `Y = y` for a polynomial
`y : R[X]` lands `W(X, Y)` in `R[X]`, where `Polynomial.derivative` is the derivative in `X`, and
it differentiates to `W_X(X, y) + W_Y(X, y) · y'`. -/
@[simp]
lemma derivative_eval_polynomial (y : R[X]) :
    derivative (W.polynomial.eval y)
      = W.polynomialX.eval y + W.polynomialY.eval y * derivative y := by
  -- Mathlib's generic chain rule for a derivation applied to `eval`, at `Polynomial.derivative'`.
  have h := (derivative' (R := R)).apply_eval_eq y W.polynomial
  simp only [derivative'_apply] at h
  rw [h, eval_mapCoeffs_polynomial, derivative_polynomial, smul_eq_mul]

/-- **The `X`-partial derivative of the Weierstrass polynomial is the `Polynomial.derivative` of
its specialisation at a constant.** This is the chain rule with `y' = 0`. -/
-- Not `@[simp]`: `simp` reaches it from `derivative_eval_polynomial` and `derivative_C`.
lemma derivative_eval_polynomial_C (y : R) :
    derivative (W.polynomial.eval (C y)) = W.polynomialX.eval (C y) := by
  simp

end WeierstrassCurve.Affine

end TauCeti

end
