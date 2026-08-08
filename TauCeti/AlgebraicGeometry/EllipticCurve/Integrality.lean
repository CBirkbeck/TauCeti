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
(`sq_dvd_den_of_prime_of_dvd`), so any prime dividing it divides it twice, hence divides
`f.leadingCoeff` twice. If that leading coefficient is squarefree, no prime can divide the
denominator at all, so `den x` is a unit and `x` is integral.

The second is a consequence of the curve equation alone: once `x` comes from `R`, `y` is a root of
the monic quadratic `Y² + (a₁x + a₃)Y − (x³ + a₂x² + a₄x + a₆)` over `R`, so `y` is integral over
`R`. That step needs no domain, fraction-field or factorisation hypothesis, so it is stated over an
arbitrary `R`-algebra, with the fraction-field version as a corollary.

## Main results

* `TauCeti.WeierstrassCurve.isInteger_of_is_root_of_squarefree_leadingCoeff`: the `x`-coordinate of
  a point is integral if it is a root of a polynomial over `R` with squarefree leading coefficient.
* `TauCeti.WeierstrassCurve.isIntegral_y_of_equation_of_mem_range`: over **any** `R`-algebra, a
  point whose `x`-coordinate comes from `R` has `y`-coordinate integral over `R`.
* `TauCeti.WeierstrassCurve.isInteger_y_of_equation_of_isInteger_x`: its fraction-field corollary,
  the shape the Nagell–Lutz argument consumes.

Both are stated for an arbitrary point: no torsion, ellipticity or minimality hypothesis. In the
Nagell–Lutz argument the polynomial `f` is a division polynomial, whose leading coefficient is the
order of the torsion point.

This advances the Nagell–Lutz integrality milestone of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz".

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned by
that roadmap at `dev/modular-curves @ 9fec8eba7652`:
`LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean`, declarations
`isInteger_of_root_squarefree_leading_coeff` and `y_isInteger_of_x_isInteger_on_curve`. The latter
is generalised here from the fraction field to an arbitrary `R`-algebra.
-/

public section

open Polynomial IsFractionRing

namespace TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve R)

/-- **An integral `x`-coordinate forces an integral `y`-coordinate**, over any `R`-algebra.

On the curve, `y` is a root of the monic quadratic `Y² + (a₁x₀ + a₃)Y − (x₀³ + a₂x₀² + a₄x₀ + a₆)`
over `R`, so `y` is integral over `R`. No domain, fraction-field or factorisation hypothesis is
needed — only that the `x`-coordinate comes from `R`.

(The variant assuming merely `IsIntegral R x` also holds, by running this argument over
`Algebra.adjoin R {x}` and applying `isIntegral_trans`; it is not needed by the Nagell–Lutz route,
where the `x`-coordinate is genuinely an element of `R`.) -/
theorem isIntegral_y_of_equation_of_mem_range {A : Type*} [CommRing A] [Algebra R A] {x y : A}
    (h : (W.baseChange A).toAffine.Equation x y) {x₀ : R} (hx₀ : algebraMap R A x₀ = x) :
    IsIntegral R y := by
  refine ⟨X ^ 2 + (C (W.a₁ * x₀ + W.a₃) * X + C (-(x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))),
    monic_X_pow_add (by compute_degree!), ?_⟩
  rw [_root_.WeierstrassCurve.Affine.equation_iff] at h
  simp only [_root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_a₁,
    _root_.WeierstrassCurve.map_a₂, _root_.WeierstrassCurve.map_a₃,
    _root_.WeierstrassCurve.map_a₄, _root_.WeierstrassCurve.map_a₆] at h
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_neg, map_add, map_mul,
    map_pow, map_neg]
  rw [← hx₀] at h
  linear_combination h

section FractionField

variable [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {x y : K}

/-- **The rational-root integrality step.** If the `x`-coordinate of a point of `W` is a root of
`f ∈ R[X]` and `f.leadingCoeff` is squarefree, then `x` is integral.

The rational root theorem gives `den x ∣ f.leadingCoeff`; powerfulness of the denominator
(`sq_dvd_den_of_prime_of_dvd`) upgrades any prime factor `q` of `den x` to `q * q ∣ f.leadingCoeff`,
which squarefreeness forbids. -/
theorem isInteger_of_is_root_of_squarefree_leadingCoeff
    (h : (W.baseChange K).toAffine.Equation x y) {f : R[X]} (hroot : aeval x f = 0)
    (hsf : Squarefree f.leadingCoeff) : IsLocalization.IsInteger R x := by
  refine isInteger_of_isUnit_den ?_
  by_contra hnu
  obtain ⟨q, hq_irr, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu
    (mem_nonZeroDivisors_iff_ne_zero.mp (den R x).2)
  have hq : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq_irr
  have hden : q * q ∣ (den R x : R) := by
    rw [← pow_two]; exact sq_dvd_den_of_prime_of_dvd W h hq hq_dvd
  exact hq.not_isUnit (hsf q (hden.trans (den_dvd_of_is_root hroot)))

/-- **On the curve over a fraction field, an integral `x`-coordinate forces an integral
`y`-coordinate.** The `IsLocalization.IsInteger` form of `isIntegral_y_of_equation_of_mem_range`,
which is the shape the Nagell–Lutz argument consumes. -/
theorem isInteger_y_of_equation_of_isInteger_x (h : (W.baseChange K).toAffine.Equation x y)
    (hx : IsLocalization.IsInteger R x) : IsLocalization.IsInteger R y := by
  obtain ⟨x₀, hx₀⟩ := hx
  exact RingHom.mem_rangeS.mpr (IsIntegrallyClosed.isIntegral_iff.mp
    (isIntegral_y_of_equation_of_mem_range W h hx₀))

end FractionField

end WeierstrassCurve

end TauCeti
