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
`RatFunc F` itself once `RatFunc.liftAlgebra` is in scope. This file computes it: on a function
regular away from infinity it is the polynomial norm, and on a function of `x` alone it is the
square.

## Main results

* `WeierstrassCurve.Affine.norm_algebraMap_coordinateRing`: on an element of the coordinate
  ring the norm is `Algebra.norm R[X]`, read as a rational function.
* `WeierstrassCurve.Affine.norm_algebraMap_eq_sq`: on a rational function of `x` the norm is its
  square, the extension being quadratic.
* `WeierstrassCurve.Affine.intDegree_norm_algebraMap_coordinateRing`: consequently the
  `intDegree` of the norm of a function regular away from infinity is the degree of its polynomial
  norm.

No new norm is defined: `Algebra.norm L` is the norm, and multiplicativity, `map_one` and vanishing
exactly at `0` are Mathlib's `map_mul`, `map_one` and `Algebra.norm_eq_zero_iff`. What is new is the
two computations. They sit at the level of `finrank_functionField`, which they use — an integral
domain of coefficients and an arbitrary fraction field `L` of `R[X]` — so they serve `RatFunc R` and
`FractionRing R[X]` alike. Only the degree corollary forces `RatFunc`: the degree theory of rational
functions, `RatFunc.intDegree` and with it Mathlib's place at infinity `RatFunc.inftyValuation`, is
stated for no other fraction field.

`RatFunc.liftAlgebra` is a *scoped* instance in Mathlib, because it would create a diamond when the
extension is `RatFunc F` itself; files consuming these results open the `RatFunc` scope as this one
does. The repository's own `algebraFractionRingFunctionField` is the same construction for
`FractionRing F[X]`, exported there because that diamond cannot arise for a quadratic extension.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors).
The layer asks for the place at infinity, "where `x` and `y` have their poles", with `ord_∞ x = -2`,
`ord_∞ y = -3` and residue field `K`. That place is this norm followed by Mathlib's place at
infinity of `F(x)`: `ord_∞ f = -deg N(f)`, so `v_∞ = RatFunc.inftyValuation ∘ Algebra.norm`. This
file is the norm's computation; the valuation itself and the two coordinate orders come next. Layer
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

open scoped RatFunc

namespace WeierstrassCurve.Affine

section Domain

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

end Domain

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
