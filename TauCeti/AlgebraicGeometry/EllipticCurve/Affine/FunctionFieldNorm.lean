/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.Localization.NormTrace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionFieldFinrank

/-!
# The norm of a function on a Weierstrass curve, as a rational function

The function field `F(W)` of an affine Weierstrass curve is a quadratic extension of the rational
function field `F(x)` — that is `TauCeti.WeierstrassCurve.Affine.finrank_functionField` — so every
function has an algebra norm there. This file records that norm as a map into `RatFunc F` and
computes it on functions coming from the coordinate ring.

## Main definitions

* `TauCeti.WeierstrassCurve.Affine.normRatFunc`: the algebra norm
  `N : F(W) → F(x)`, as a monoid homomorphism valued in `RatFunc F`.

## Main results

* `TauCeti.WeierstrassCurve.Affine.normRatFunc_eq_zero_iff`: the norm vanishes only at `0`.
* `TauCeti.WeierstrassCurve.Affine.normRatFunc_algebraMap`: on a function regular away from
  infinity — an element of the coordinate ring — it is the polynomial norm `Algebra.norm F[X]`.
* `TauCeti.WeierstrassCurve.Affine.intDegree_normRatFunc_algebraMap`: consequently its `intDegree`
  is the degree of that polynomial norm.

`Mathlib`'s `Algebra.norm` already lands in `FractionRing F[X]`, and the two are the same field.
The point of transporting it to `RatFunc F` once, here, is that the degree theory of rational
functions is stated only for `RatFunc`: `RatFunc.intDegree`, and with it Mathlib's place at
infinity `RatFunc.inftyValuation`, are not available on `FractionRing F[X]`. Landing there keeps
every later degree computation a rewrite rather than a transport.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors).
The layer asks for the place at infinity, "where `x` and `y` have their poles", with `ord_∞ x = -2`,
`ord_∞ y = -3`. That place is built from this norm: `ord_∞ f = -deg N(f)`, so `v_∞` is Mathlib's
`RatFunc.inftyValuation` composed with `normRatFunc`. This file is that norm and its degree; the
valuation itself, and the two coordinate orders, come next. Layer 0 seeds no declaration this
competes with — `Suggested.lean` records that the function-field layer's "types are new API and are
built there, not pinned here".

## Provenance

The route is that of the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil` at `a582951fe96b`), `HasseWeil/Curves/Infinity.lean`, declarations `normAsRatFunc`,
`normAsRatFunc_mul` and `normAsRatFunc_eq_zero_iff`.

Changes from the source. There the norm is taken over a `SmoothPlaneCurve` structure wrapping
`WeierstrassCurve.Affine`, through that development's own `fieldNorm`; here it is Mathlib's
`Algebra.norm` over `FractionRing F[X]`, transported by `RatFunc.toFractionRingAlgEquiv`, and stated
directly about `W.FunctionField`. Multiplicativity is not restated: bundling the norm as a
`MonoidHom` makes `map_mul` and `map_one` Mathlib's. The compatibility with the polynomial norm is
`Algebra.norm_localization`, which the source proves by hand for its own norm.
-/

public section

open Polynomial WeierstrassCurve

namespace TauCeti

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : _root_.WeierstrassCurve.Affine F)

/-- **The norm of a function on a Weierstrass curve, as a rational function of `x`.** The function
field is a quadratic extension of `F(x)` (`finrank_functionField`), and this is its algebra norm,
carried along `RatFunc.toFractionRingAlgEquiv` into `RatFunc F` where the degree theory of rational
functions lives. Bundled as a monoid homomorphism, so multiplicativity is `map_mul`. -/
noncomputable def normRatFunc : W.FunctionField →* RatFunc F :=
  (RatFunc.toFractionRingAlgEquiv (K := F) F[X]).symm.toRingEquiv.toRingHom.toMonoidHom.comp
    (Algebra.norm (FractionRing F[X]))

/-- **The norm of a function vanishes only at `0`.** -/
@[simp]
theorem normRatFunc_eq_zero_iff {f : W.FunctionField} : normRatFunc W f = 0 ↔ f = 0 := by
  rw [normRatFunc]
  simp [Algebra.norm_eq_zero_iff (R := FractionRing F[X])]

/-- **On a function regular away from infinity the norm is the polynomial norm**: for `u` in the
coordinate ring, `N u` is `Algebra.norm F[X] u` read as a rational function. -/
@[simp]
theorem normRatFunc_algebraMap (u : W.CoordinateRing) :
    normRatFunc W (algebraMap W.CoordinateRing W.FunctionField u) =
      algebraMap F[X] (RatFunc F) (Algebra.norm F[X] u) := by
  rw [normRatFunc, MonoidHom.coe_comp, Function.comp_apply]
  rw [show (Algebra.norm (FractionRing F[X])) (algebraMap W.CoordinateRing W.FunctionField u) =
      algebraMap F[X] (FractionRing F[X]) (Algebra.norm F[X] u) from
    Algebra.norm_localization (R := F[X]) (M := nonZeroDivisors F[X]) (S := W.CoordinateRing) u]
  exact (RatFunc.toFractionRingAlgEquiv (K := F) F[X]).symm.commutes _

/-- **The degree of the norm of a function regular away from infinity** is the degree of its
polynomial norm. This is the input to the order at infinity, `ord_∞ f = -deg N f`. -/
theorem intDegree_normRatFunc_algebraMap (u : W.CoordinateRing) :
    (normRatFunc W (algebraMap W.CoordinateRing W.FunctionField u)).intDegree =
      (Algebra.norm F[X] u).natDegree := by
  rw [normRatFunc_algebraMap, RatFunc.intDegree_polynomial]

end WeierstrassCurve.Affine

end TauCeti

end
