/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Polynomial.RationalRoot
public import TauCeti.AlgebraicGeometry.EllipticCurve.Denominator

/-!
# Integrality of points on a Weierstrass curve over a unique factorization domain

Let `R` be a unique factorization domain with fraction field `K` and let `W : WeierstrassCurve R`
have coefficients in `R`. This file gives the two integrality steps of the Nagell–Lutz argument
that do not mention torsion.

The first is the rational-root step. If the `x`-coordinate of a `K`-point is a root of some
`f ∈ R[X]`, the rational root theorem bounds its denominator: `den x ∣ f.leadingCoeff`. On its own
that is far from integrality — but the denominator of a point is *powerful*
(`sq_dvd_den_of_prime_dvd`), so any prime dividing it divides it twice, hence divides
`f.leadingCoeff` twice. If that leading coefficient is squarefree, no prime can divide the
denominator at all, so `den x` is a unit and `x` is integral.

The second is a one-line consequence of the curve equation: once `x` is integral, `y` is a root of
the monic quadratic `Y² + (a₁x + a₃)Y − (x³ + a₂x² + a₄x + a₆)` over `R`, so `y` is integral too.

## Main results

* `TauCeti.WeierstrassCurve.isInteger_of_aeval_eq_zero_of_squarefree_leadingCoeff`: the
  `x`-coordinate of a point is integral if it is a root of a polynomial over `R` with squarefree
  leading coefficient.
* `TauCeti.WeierstrassCurve.isInteger_of_equation_of_isInteger`: on the curve, an integral
  `x`-coordinate forces an integral `y`-coordinate.

Both are stated for an arbitrary point: no torsion, ellipticity or minimality hypothesis. In the
Nagell–Lutz argument the polynomial `f` is a division polynomial, whose leading coefficient is the
order of the torsion point.

This advances the Nagell–Lutz integrality milestone of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz".

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned by
that roadmap at `dev/modular-curves @ 9fec8eba7652`:
`LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean`, declarations
`isInteger_of_root_squarefree_leading_coeff` and `y_isInteger_of_x_isInteger_on_curve`.
-/

public section

open Polynomial IsFractionRing

namespace TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (W : _root_.WeierstrassCurve R) {x y : K}

/-- **The rational-root integrality step.** If the `x`-coordinate of a point of `W` is a root of
`f ∈ R[X]` and `f.leadingCoeff` is squarefree, then `x` is integral.

The rational root theorem gives `den x ∣ f.leadingCoeff`; powerfulness of the denominator
(`sq_dvd_den_of_prime_dvd`) upgrades any prime factor `q` of `den x` to `q * q ∣ f.leadingCoeff`,
which squarefreeness forbids. -/
theorem isInteger_of_aeval_eq_zero_of_squarefree_leadingCoeff
    (h : (W.baseChange K).toAffine.Equation x y) {f : R[X]} (hroot : aeval x f = 0)
    (hsf : Squarefree f.leadingCoeff) : IsLocalization.IsInteger R x := by
  refine isInteger_of_isUnit_den ?_
  by_contra hnu
  obtain ⟨q, hq_irr, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu
    (mem_nonZeroDivisors_iff_ne_zero.mp (den R x).2)
  have hq : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq_irr
  have hden : q * q ∣ (den R x : R) := by
    rw [← pow_two]; exact sq_dvd_den_of_prime_dvd W h hq hq_dvd
  exact hq.not_isUnit (hsf q (hden.trans (den_dvd_of_is_root hroot)))

/-- **An integral `x`-coordinate forces an integral `y`-coordinate.** On the curve, `y` is a root
of the monic quadratic `Y² + (a₁x + a₃)Y − (x³ + a₂x² + a₄x + a₆)` over `R`. -/
theorem isInteger_of_equation_of_isInteger (h : (W.baseChange K).toAffine.Equation x y)
    (hx : IsLocalization.IsInteger R x) : IsLocalization.IsInteger R y := by
  obtain ⟨x₀, hx₀⟩ := hx
  set c₁ : R := W.a₁ * x₀ + W.a₃ with hc₁
  set c₀ : R := -(x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hc₀
  refine isInteger_of_is_root_of_monic (p := X ^ 2 + (C c₁ * X + C c₀))
    (monic_X_pow_add (by compute_degree!)) ?_
  rw [_root_.WeierstrassCurve.Affine.equation_iff] at h
  simp only [_root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_a₁,
    _root_.WeierstrassCurve.map_a₂, _root_.WeierstrassCurve.map_a₃,
    _root_.WeierstrassCurve.map_a₄, _root_.WeierstrassCurve.map_a₆] at h
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, hc₁, hc₀, map_neg]
  rw [← hx₀] at h
  linear_combination h

end WeierstrassCurve

end TauCeti
