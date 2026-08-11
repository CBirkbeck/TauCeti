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
`RatFunc F` itself once `RatFunc.liftAlgebra` is in scope. This file computes the degree of that
norm on the two coordinate functions: `N x = x ^ 2` has degree `2`, and `N y`, the negative of the
cubic the Weierstrass equation solves for, has degree `3`.

## Main results

* `WeierstrassCurve.Affine.natDegree_norm_X`, `WeierstrassCurve.Affine.natDegree_norm_mk_Y`: the
  norms of the two coordinate functions have degrees `2` and `3`.
* `WeierstrassCurve.Affine.intDegree_norm_algebraMap_coordinateRing`: over `RatFunc F`, the
  `intDegree` of the norm of a function regular away from infinity is the degree of its polynomial
  norm.


No new norm is defined, and no lemma restates a generic one: `Algebra.norm` is the norm,
multiplicativity and vanishing exactly at `0` are `map_mul` and `Algebra.norm_eq_zero_iff`, and the
value of the norm on the base ring and on the coordinate ring is `Algebra.norm_algebraMap` and
`Algebra.norm_localization`, applied where they are needed rather than re-exported. What is new are the two
coordinate degrees, which are curve-specific and which Mathlib does not state.

Only the last result forces `RatFunc`: the degree theory of rational functions, `RatFunc.intDegree`
and with it Mathlib's place at infinity `RatFunc.inftyValuation`, is stated for no other fraction
field of `F[X]`.

`RatFunc.liftAlgebra` is a *scoped* instance in Mathlib, because it would create a diamond when the
extension is `RatFunc F` itself; files consuming these results open the `RatFunc` scope as this one
does. The repository's own `algebraFractionRingFunctionField` is the same construction for
`FractionRing F[X]`, exported there because that diamond cannot arise for a quadratic extension.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors).
The layer asks for the place at infinity, "where `x` and `y` have their poles", with `ord_∞ x = -2`,
`ord_∞ y = -3` and residue field `K`. That place is this norm followed by Mathlib's place at
infinity of `F(x)`: `ord_∞ f = -deg N(f)`, so `v_∞ = RatFunc.inftyValuation ∘ Algebra.norm`. This
file supplies the degrees that `ord_∞` is computed from: `ord_∞ f = -deg N f`, so the degrees `2`
and `3` proved here are what will give `ord_∞ x = -2` and `ord_∞ y = -3` once the valuation exists.
The valuation itself, whose content is the ultrametric inequality, comes next; no order at infinity
is defined or claimed in this file. Layer
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

section Nontrivial

-- Both degrees read the norm off the `1, Y` basis with `norm_smul_basis`, an identity over any
-- commutative ring, so a nontrivial base is all they need.
variable {R : Type*} [CommRing R] [Nontrivial R] (W : _root_.WeierstrassCurve.Affine R)

/-- **The norm of the coordinate function `x` has degree `2`**: it is `x ^ 2`. -/
@[simp]
theorem natDegree_norm_X :
    (Algebra.norm R[X] (algebraMap R[X] W.CoordinateRing X)).natDegree = 2 := by
  -- `norm_smul_basis` reads the norm off the `1, Y` basis, so `x` is written in it first
  have hX : algebraMap R[X] W.CoordinateRing X =
      (X : R[X]) • (1 : W.CoordinateRing) + (0 : R[X]) • CoordinateRing.mk W Y := by
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one]
  rw [hX, CoordinateRing.norm_smul_basis]
  simp

/-- **The norm of the coordinate function `y` has degree `3`**, being the negative of the cubic in
`x` that the Weierstrass equation solves for. -/
@[simp]
theorem natDegree_norm_mk_Y :
    (Algebra.norm R[X] (CoordinateRing.mk W Y)).natDegree = 3 := by
  -- `norm_smul_basis` reads the norm off the `1, Y` basis, so `y` is written in it first
  have hY : CoordinateRing.mk W Y = (0 : R[X]) • 1 + (1 : R[X]) • CoordinateRing.mk W Y := by simp
  rw [hY, CoordinateRing.norm_smul_basis]
  compute_degree!

end Nontrivial

variable {F : Type*} [Field F] (W : _root_.WeierstrassCurve.Affine F)

/-- **The degree of the norm of a function regular away from infinity**, as a rational function, is
the degree of its polynomial norm. This is what the order at infinity is computed from, and it is
where `RatFunc F` is forced: `intDegree` is stated for no other fraction field of `F[X]`. -/
@[simp]
theorem intDegree_norm_algebraMap_coordinateRing (u : W.CoordinateRing) :
    (Algebra.norm (RatFunc F) (algebraMap W.CoordinateRing W.FunctionField u)).intDegree =
      (Algebra.norm F[X] u).natDegree := by
  rw [Algebra.norm_localization (R := F[X]) (M := nonZeroDivisors F[X]) (S := W.CoordinateRing),
    RatFunc.intDegree_polynomial]

end WeierstrassCurve.Affine

end
