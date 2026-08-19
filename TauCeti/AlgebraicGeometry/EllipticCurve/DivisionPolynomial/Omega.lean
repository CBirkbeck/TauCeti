/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Invariant
public import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.ReducedInvariant

/-!
# The omega family of division polynomials

`ω n` is the bivariate polynomial giving the second (Jacobian) coordinate of scalar
multiplication by `n` on a Weierstrass curve, completing the `(φ, ψ)` pair of Mathlib's
division-polynomial API. This file defines `ω` and the 2-complement `ψc` of `ψ`, and proves
the identity that pins `ω` down,

`2 ω n + a₁ φ n ψ n + a₃ (ψ n)³ = ψc n`,

together with the value lemmas `ω_zero` and `ω_one`, the parity rules `ω_neg` and `ψc_neg`,
the complement identity `ψ n * ψc n = ψ (2n)`, naturality in the coefficient ring, and the
ellipticity of the `ψ` family itself.

## Main definitions

* `WeierstrassCurve.ψc`: the complement of `ψ n` in `ψ (2n)`.
* `WeierstrassCurve.ω`: the `ω` family of division polynomials.

## Main results

* `WeierstrassCurve.ω_spec`: `2 ω n + a₁ φ n ψ n + a₃ (ψ n)³ = ψc n`.
* `WeierstrassCurve.ψ_mul_ψc`: `ψ n * ψc n = ψ (2n)`.
* `WeierstrassCurve.ω_neg`: `ω (-n) = ω n + a₁ φ n ψ n + a₃ (ψ n)³`, proved over the
  universal curve — where `2` is a nonzerodivisor — and specialised.
* `WeierstrassCurve.isEllipticSequence_ψ`: the `ψ` family is an elliptic sequence.

## Provenance

Ported from J. Xu and D. K. Angdinata's `LutzNagell/DivisionPolynomialOmega.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `ψc`, `ω`, `ω_spec`, `two_mul_ω`,
`ψc_spec` (here `ψ_mul_ψc`, naming its left-hand side), `ω_zero`, `ω_one`, `ψc_neg`,
`map_ω`, `universal_ω_neg`, `ω_neg` and `isEllSequence_ψ` (here `isEllipticSequence_ψ`,
matching Mathlib's predicate name). That file's header reads
`Authors: Junyan Xu, David Kurniadi Angdinata`; following this repository's convention for
adapted material the upstream authorship is credited here rather than in the copyright
header. The invariant-polynomial half of that source file is already in
`DivisionPolynomial/Invariant.lean`; this file is the `ω` half, unblocked by
`reducedInvarNum_eq_reducedInvarDenom_mul` (`ReducedInvariant.lean`), the port of the
source's `redInvar_normEDS`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

public section

noncomputable section

open Affine (polynomial polynomialX polynomialY negPolynomial)

/-- The `ψ` family is `normEDS` at the curve's division-polynomial parameters, stated at the
level of functions so that both applied and unapplied occurrences of `ψ` rewrite. -/
theorem ψ_eq_normEDS : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl

/-- The `ψ` family of division polynomials is an elliptic sequence: it is `normEDS` at the
curve's parameters, and a normalised EDS is an elliptic sequence. -/
theorem isEllipticSequence_ψ : IsEllipticSequence W.ψ := by
  rw [ψ_eq_normEDS]
  exact isEllipticSequence_normEDS _ _ _

/-- The complement of `ψ n` in `ψ (2n)`: the parameter-level `complEDS₂` at the curve's
division-polynomial parameters. `ψ_mul_ψc` below is the identity it is named for. -/
def ψc : ℤ → R[X][Y] := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

/-- The defining formula for `ψc`, at the level of functions. The definition body is not
exposed, so this equation lemma is how a consumer in another module computes with it. -/
theorem ψc_def : W.ψc = complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := (rfl)

/-- The `ω` family of division polynomials: `ω n` gives the second coordinate in Jacobian
coordinates of scalar multiplication by `n`. -/
protected def ω (n : ℤ) : R[X][Y] :=
  reducedInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
  - complEDS₂Aux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3

/-- **The defining identity of `ω`**:
`2 ω n + a₁ φ n ψ n + a₃ (ψ n)³ = ψc n`. -/
theorem ω_spec (n : ℤ) :
    2 * W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n := by
  rw [ψc, complEDS₂_eq_reducedInvarNum_sub, reducedInvarNum_eq_reducedInvarDenom_mul,
    preΨ₄_add_ψ₂_pow_four, mul_assoc (C _), φ_mul_ψ, ψ_eq_normEDS,
    IsEllipticNet.invarDenom_normEDS_one_eq_reducedInvarDenom_mul, WeierstrassCurve.ω,
    ← ψ_eq_normEDS, invar_def, b₂, b₄, ψ₂, polynomialY, polynomialX, negPolynomial]
  simp only [map_ofNat, C_add, C_mul, C_pow]
  ring

theorem two_mul_ω (n : ℤ) :
    2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ω_spec]; abel

/-- `ψ n * ψc n = ψ (2n)`: the complement identity `ψc` is named for. -/
theorem ψ_mul_ψc (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) :=
  normEDS_mul_complEDS₂ _ _ _ _

@[simp] theorem ω_zero : W.ω 0 = 1 := by simp [WeierstrassCurve.ω, complEDS₂Aux_def]

@[simp] theorem ω_one : W.ω 1 = Y := by
  simp [WeierstrassCurve.ω, ψ₂, complEDS₂Aux_def, ← Affine.Y_sub_polynomialY]
  ring

@[simp] theorem ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by simp [ψc]

end

section Map

open Affine in
@[simp]
theorem map_ω (f : R →+* S) (n : ℤ) : (W.map f).ω n = (W.ω n).map (mapRingHom f) := by
  simp_rw [WeierstrassCurve.ω, ← coe_mapRingHom, map_add, map_sub, map_mul,
    map_reducedInvarDenom, map_complEDS₂Aux, map_polynomial, map_polynomialX, map_polynomialY,
    map_negPolynomial, map_ψ₂, map_Ψ₃, map_preΨ₄, map_Ψ₂Sq, map_ψ]
  simp

open Universal in
/-- `ω_neg` over the universal curve, where the coefficient ring is a domain and `2` is a
nonzerodivisor, so the identity may be doubled and read off `two_mul_ω`. -/
private theorem universal_ω_neg (n : ℤ) :
    curve.ω (-n) = curve.ω n + CC curve.a₁ * curve.φ n * curve.ψ n
      + CC curve.a₃ * curve.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (two_ne_zero (α := Universal.Poly)))]
  simp_rw [left_distrib, two_mul_ω, ψc_neg, ψ_neg, φ_neg]
  ring

open Universal in
/-- The parity rule for `ω`, specialised from the universal curve. -/
theorem ω_neg (n : ℤ) :
    W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← W.map_specialize, map_ω, universal_ω_neg, map_φ, map_ω, map_ψ]
  simp

end Map

end

end WeierstrassCurve
