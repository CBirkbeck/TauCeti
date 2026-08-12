/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Invariant

/-!
# The invariant polynomial of a Weierstrass curve

The quotient `(ψ(n-1)² ψ(n+2) + ψ(n-2) ψ(n+1)² + ψ₂² ψ(n)³) / (ψ(n+1) ψ(n) ψ(n-1))` is, modulo the
Weierstrass polynomial, independent of `n` — it is the invariant of the elliptic net `ψ`, and its
value is the polynomial

`WeierstrassCurve.invar = 6 X² + b₂ X + b₄`.

This file defines that polynomial and proves the division-polynomial identities that identify it,
together with the one identity connecting `φ` and `ψ` to `IsEllipticNet.invarDenom`. They are the
first stage of the `ω` family of division polynomials, which gives the `Y` coordinate of scalar
multiplication in Jacobian coordinates.

## Main definitions

* `WeierstrassCurve.invar`: the invariant polynomial `6 X² + b₂ X + b₄`.

## Main results

* `WeierstrassCurve.preΨ₄_add_Ψ₂Sq_sq`: `preΨ₄ + Ψ₂Sq ^ 2 = invar * Ψ₃`, the identity that pins
  `invar` down. Its certificate is the `b`-relation `4 b₈ = b₂ b₆ - b₄ ²`.
* `WeierstrassCurve.preΨ₄_add_ψ₂_pow_four`: the same identity in the bivariate ring, where it
  acquires a multiple of the Weierstrass polynomial.
* `WeierstrassCurve.C_Ψ₃_eq`: `Ψ₃` through the partial derivatives of the Weierstrass polynomial.
* `WeierstrassCurve.φ_mul_ψ`: `φ n * ψ n = X ψ(n)³ - invarDenom ψ 1 n`, which is what connects the
  division polynomials to the invariant of the elliptic net they form.

## What is deliberately not here

`WeierstrassCurve.ω` itself and its API — `ω_spec`, `two_mul_ω`, `ψc`, `ψc_spec`, `ω_zero`,
`ω_one`, `ψc_neg`, `map_ω`, `ω_neg` — are **not** in this file. `ω` is defined through
`redInvarDenom` and `complEDS₂Aux`, and `ω_spec` additionally consumes `redInvar_normEDS`, which
routes through `normEDS` being an elliptic sequence: a fact the pinned Mathlib records as an open
TODO and whose proof is the parity-transfer machinery of Mathlib PR #42453. Nothing in this file
depends on any of it, so the identities land now and `ω` follows when that gap closes.

## Provenance

Ported from J. Xu and D. K. Angdinata's `LutzNagell/DivisionPolynomialOmega.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `invar`, `C_Ψ₃_eq`,
`preΨ₄_add_Ψ₂Sq_sq`, `preΨ₄_add_ψ₂_pow_four` and `φ_mul_ψ`. That file's header reads
`Authors: Junyan Xu, David Kurniadi Angdinata`; following this repository's convention for adapted
material the upstream authorship is credited here rather than in the copyright header.

Two adaptations, neither of them a choice:

* the source proves `φ_mul_ψ` by `rw [φ, invarDenom]`, unfolding both definitions. The
  `invarDenom` half does not port: `EllipticDivisibilitySequence/Invariant.lean` exports that body
  unexposed, so from this module `rw [invarDenom]` has nothing to rewrite with. It goes through the
  equation lemma `IsEllipticNet.invarDenom_def` instead. `φ` unfolds as before, being Mathlib's.
* the source's local `C_simp` macro is written out at its three use sites rather than carried
  across, a macro being more surface than the one `simp only` call it abbreviates.

The statement of `φ_mul_ψ` was checked against Mathlib's `φ` rather than assumed: Mathlib defines
`φ n = C X * ψ n ^ 2 - ψ (n + 1) * ψ (n - 1)`, so `φ n * ψ n` is
`C X * ψ n ^ 3 - ψ (n + 1) * ψ n * ψ (n - 1)`, and that subtrahend is exactly
`IsEllipticNet.invarDenom ψ 1 n`.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The invariant polynomial `6 X² + b₂ X + b₄` of a Weierstrass curve: modulo the Weierstrass
polynomial it is the value of the invariant of the elliptic net `ψ`, the quotient
`(ψ(n-1)² ψ(n+2) + ψ(n-2) ψ(n+1)² + ψ₂² ψ(n)³) / (ψ(n+1) ψ(n) ψ(n-1))` for any `n`. -/
noncomputable def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- The defining formula for `invar`. The definition body is not exposed, so this equation lemma is
how a consumer computes with it. Not `@[simp]`: the point of naming the polynomial is that
`preΨ₄_add_Ψ₂Sq_sq` can be stated over it, which unfolding everywhere would defeat. -/
theorem invar_def : W.invar = 6 * X ^ 2 + C W.b₂ * X + C W.b₄ := (rfl)

/-- `Ψ₃` expressed through the partial derivatives of the Weierstrass polynomial. -/
theorem C_Ψ₃_eq :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - Affine.polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * Affine.polynomialX W - CC W.a₁ ^ 2 * Affine.polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, Affine.polynomial, Affine.polynomialX, ψ₂, Affine.polynomialY, b₂, b₄, b₆, b₈,
    CC]
  simp only [map_ofNat, C_add, C_sub, C_mul, C_pow]
  ring

/-- **The identity that pins `invar` down**: `preΨ₄ + Ψ₂Sq ^ 2 = invar * Ψ₃`. The certificate is
the `b`-relation `4 * b₈ = b₂ * b₆ - b₄ ^ 2`. -/
theorem preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm := (simp only [map_ofNat, C_sub, C_mul, C_pow]; ring_nf))
    congr(C $W.b_relation) * (@X R _) ^ 2

/-- The bivariate form of `preΨ₄_add_Ψ₂Sq_sq`. Passing to `R[X][Y]` costs a multiple of the
Weierstrass polynomial, `ψ₂ ^ 2` and `C Ψ₂Sq` differing by `8` times it. -/
theorem preΨ₄_add_ψ₂_pow_four : C W.preΨ₄ + W.ψ₂ ^ 4 =
    C (W.invar * W.Ψ₃) + 8 * Affine.polynomial W * (2 * Affine.polynomial W + C W.Ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq, ← add_assoc, ← C_pow, ← C_add,
    preΨ₄_add_Ψ₂Sq_sq]
  simp only [C_mul]
  ring

/-- **The division polynomials meet the invariant of their elliptic net**: `φ n * ψ n` is
`X ψ(n)³` less the invariant's denominator at `s = 1`. This is the step through which the
elliptic-net identities reach the curve. -/
theorem φ_mul_ψ (n : ℤ) :
    W.φ n * W.ψ n = C X * W.ψ n ^ 3 - IsEllipticNet.invarDenom W.ψ 1 n := by
  rw [WeierstrassCurve.φ, IsEllipticNet.invarDenom_def]
  ring

end WeierstrassCurve
