/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.Localization.NormTrace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank

/-!
# The norm of a function on a Weierstrass curve

The function field `F(W)` of an affine Weierstrass curve is a quadratic extension of the rational
function field `F(x)` — that is `WeierstrassCurve.Affine.finrank_functionField` — so every
function has an algebra norm `N : F(W) → F(x)`. Mathlib's `Algebra.norm` supplies it, over
`RatFunc F` itself once `RatFunc.liftAlgebra` is in scope. This file computes it and its degree: on
a function regular away from infinity the norm is the polynomial norm, on a function of `x` alone it
is the square, and the degree of the norm of `p + qY` is `max (2 deg p) (2 deg q + 3)` — whence the
poles of the two coordinate functions at infinity, `x` double and `y` triple.

## Main results

* `WeierstrassCurve.Affine.norm_algebraMap_coordinateRing`: on an element of the coordinate
  ring the norm is `Algebra.norm R[X]`, read as a rational function.
* `WeierstrassCurve.Affine.norm_algebraMap_eq_sq`: on a rational function of `x` the norm is its
  square, the extension being quadratic.
* `WeierstrassCurve.Affine.natDegree_norm_smul_basis`: the degree of the norm of `p + qY` is
  `max (2 * p.natDegree) (2 * q.natDegree + 3)`, for `p` and `q` both nonzero.
* `WeierstrassCurve.Affine.natDegree_norm_coordX`, `WeierstrassCurve.Affine.natDegree_norm_coordY`:
  the norms of the coordinate functions have degrees `2` and `3` — the double and triple poles at
  infinity that Layer 0 asks for.
* `WeierstrassCurve.Affine.intDegree_norm_algebraMap_coordinateRing`: consequently the
  `intDegree` of the norm of a function regular away from infinity is the degree of its polynomial
  norm.

No new norm is defined: `Algebra.norm L` is the norm, and multiplicativity, `map_one` and vanishing
exactly at `0` are Mathlib's `map_mul`, `map_one` and `Algebra.norm_eq_zero_iff`. What is new are
the computations. The first two sit at the level of `finrank_functionField`, which they use — an
integral domain of coefficients and an arbitrary fraction field `L` of `R[X]` — so they serve
`RatFunc R` and `FractionRing R[X]` alike. Only the degree corollary forces `RatFunc`: the degree
theory of rational functions, `RatFunc.intDegree` and with it Mathlib's place at infinity
`RatFunc.inftyValuation`, is stated for no other fraction field.

`RatFunc.liftAlgebra` is a *scoped* instance in Mathlib, because it would create a diamond when the
extension is `RatFunc F` itself; files consuming these results open the `RatFunc` scope as this one
does. The repository's own `algebraFractionRingFunctionField` is the same construction for
`FractionRing F[X]`, exported there because that diamond cannot arise for a quadratic extension.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors).
The layer asks for the place at infinity, "where `x` and `y` have their poles", with `ord_∞ x = -2`,
`ord_∞ y = -3` and residue field `K`. That place is this norm followed by Mathlib's place at
infinity of `F(x)`: `ord_∞ f = -deg N(f)`, so `v_∞ = RatFunc.inftyValuation ∘ Algebra.norm`. This
file is the norm and its degree, which is what `ord_∞` is built from — `natDegree_norm_coordX = 2`
and `natDegree_norm_coordY = 3` are `ord_∞ x = -2` and `ord_∞ y = -3` before the sign; the valuation
itself, whose content is the ultrametric inequality, comes next. Layer
0 seeds no declaration this competes with — `Suggested.lean` records that the function-field layer's
"types are new API and are built there, not pinned here".

## Provenance

The route is that of the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil` at `a582951fe96b`), `HasseWeil/Curves/Infinity.lean`, declarations `normAsRatFunc`
and `normAsRatFunc_mul`, together with `Curves/NormValuation.lean`.

Changes from the source. There the norm is a definition of its own — `normAsRatFunc`, built from
that development's `fieldNorm` over a `SmoothPlaneCurve` structure wrapping
`WeierstrassCurve.Affine`, with multiplicativity and vanishing proved by hand. Here there is no new
definition and no wrapper: the norm is Mathlib's over `RatFunc F`, so those three lemmas are
Mathlib's, and the coordinate-ring computation is `Algebra.norm_localization` rather than a hand
proof.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate

open scoped RatFunc

namespace WeierstrassCurve.Affine

section FractionField

-- Both computations sit at the level of `finrank_functionField`, which they use: an integral
-- domain of coefficients, and an arbitrary fraction field `L` of `R[X]` so that they serve
-- `RatFunc R` and `FractionRing R[X]` alike.
variable {R : Type*} [CommRing R] [IsDomain R] (W : _root_.WeierstrassCurve.Affine R)
  (L : Type*) [Field L] [Algebra R[X] L] [IsFractionRing R[X] L]
  [Algebra L W.FunctionField] [IsScalarTower R[X] L W.FunctionField]

/-- **On a function regular away from infinity the norm is the polynomial norm**: for `u` in the
coordinate ring, `N u` is `Algebra.norm R[X] u` read as a rational function. -/
@[simp]
theorem norm_algebraMap_coordinateRing (u : W.CoordinateRing) :
    Algebra.norm L (algebraMap W.CoordinateRing W.FunctionField u) =
      algebraMap R[X] L (Algebra.norm R[X] u) :=
  Algebra.norm_localization (R := R[X]) (M := nonZeroDivisors R[X]) (S := W.CoordinateRing) u

/-- **On a function of `x` alone the norm is the square**, the extension `R(W) / R(x)` being
quadratic. -/
@[simp]
theorem norm_algebraMap_eq_sq (r : L) :
    Algebra.norm L (algebraMap L W.FunctionField r) = r ^ 2 := by
  rw [Algebra.norm_algebraMap, finrank_functionField W L]

end FractionField

section Degree

-- The degree computations are about the coordinate ring alone; no fraction field is involved.
variable {R : Type*} [CommRing R] [IsDomain R] (W : _root_.WeierstrassCurve.Affine R)

/-- **The degree of the norm of `p + qY`**, the `natDegree` form of Mathlib's
`degree_norm_smul_basis`. Both parts must be nonzero: the `WithBot ℕ` statement reads
`max (2 • p.degree) (2 • q.degree + 3)`, and at `q = 0` the second term is `⊥` rather than `3`. -/
theorem natDegree_norm_smul_basis {p q : R[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (Algebra.norm R[X] (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W Y)).natDegree =
      max (2 * p.natDegree) (2 * q.natDegree + 3) := by
  refine natDegree_eq_of_degree_eq_some ?_
  rw [CoordinateRing.degree_norm_smul_basis, degree_eq_natDegree hp, degree_eq_natDegree hq]
  norm_cast

/-- **The norm of a function of `x` alone is its square**, the coordinate-ring form of
`norm_algebraMap_eq_sq`. -/
theorem norm_algebraMap_polynomial (p : R[X]) :
    Algebra.norm R[X] (algebraMap R[X] W.CoordinateRing p) = p ^ 2 := by
  rw [Algebra.norm_algebraMap, finrank_coordinateRing]

/-- **The coordinate function `x` has a double pole at infinity**: its norm is `x ^ 2`, of degree
`2`. -/
theorem natDegree_norm_coordX :
    (Algebra.norm R[X] (algebraMap R[X] W.CoordinateRing X)).natDegree = 2 := by
  rw [norm_algebraMap_polynomial, natDegree_pow, natDegree_X, mul_one]

/-- **The coordinate function `y` has a triple pole at infinity**: its norm is the negative of the
cubic in `x`, of degree `3`. -/
theorem natDegree_norm_coordY :
    (Algebra.norm R[X] (CoordinateRing.mk W Y)).natDegree = 3 := by
  rw [show CoordinateRing.mk W Y = (0 : R[X]) • 1 + (1 : R[X]) • CoordinateRing.mk W Y by simp,
    CoordinateRing.norm_smul_basis]
  compute_degree!

end Degree

variable {F : Type*} [Field F] (W : _root_.WeierstrassCurve.Affine F)

/-- **The degree of the norm of a function regular away from infinity** is the degree of its
polynomial norm. This is the input to the order at infinity, `ord_∞ f = -deg N f`, and it is where
`RatFunc F` is forced: `intDegree` is stated for no other fraction field of `F[X]`. -/
theorem intDegree_norm_algebraMap_coordinateRing (u : W.CoordinateRing) :
    (Algebra.norm (RatFunc F) (algebraMap W.CoordinateRing W.FunctionField u)).intDegree =
      (Algebra.norm F[X] u).natDegree := by
  rw [norm_algebraMap_coordinateRing, RatFunc.intDegree_polynomial]

end WeierstrassCurve.Affine

end
