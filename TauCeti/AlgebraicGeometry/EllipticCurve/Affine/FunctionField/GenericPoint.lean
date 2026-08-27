/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Coords
-- Proof-only: evaluation of the coordinate ring, which supplies the equation at the generic point.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval

/-!
# The generic point of an affine Weierstrass curve

The coordinate ring `W.CoordinateRing` is `R[X][Y]` modulo the Weierstrass relation, so the
classes of `X` and `Y` in the function field are a pair satisfying that relation over
`W.FunctionField`. They are the *generic point*: a point of `W` base-changed to its own function
field.

What is proved here is that the pair is a point (`equation_genericPoint`,
`equation_genericX_genericY`), that evaluating a bivariate polynomial at it is reduction modulo the
Weierstrass relation (`evalEval_genericPoint`), and that on an elliptic curve over a field the
resulting solution is nonsingular, cutting out a point `genericPoint` of `W⁄F(W)`.

The word "generic" is the usual geometric one, but no specialisation property is established:
nothing below says that a statement about this point transfers to the points of `W`, and no
consumer may rely on that.

## Main definitions

* `WeierstrassCurve.Affine.genericX`, `WeierstrassCurve.Affine.genericY`: the coordinates.
* `WeierstrassCurve.Affine.functionFieldCurve`: `W` base-changed to `W.FunctionField`.
* `WeierstrassCurve.Affine.genericPoint`: the point of `W⁄F(W)` cut out by the generic coordinates.

## Main results

* `WeierstrassCurve.Affine.equation_genericPoint` and
  `WeierstrassCurve.Affine.equation_genericX_genericY`: the generic point satisfies the equation.
* `WeierstrassCurve.Affine.nonsingular_genericPoint` and
  `WeierstrassCurve.Affine.nonsingular_genericX_genericY`: and is nonsingular, on an elliptic curve.
* `WeierstrassCurve.Affine.evalEval_genericPoint`: evaluation there is reduction.
* `WeierstrassCurve.Affine.transcendental_genericX` and
  `WeierstrassCurve.Affine.genericX_ne_algebraMap`: the coordinate `x` is transcendental
  over the base field, so it takes no constant value.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0.5**, whose third milestone asks for the
"function-field pullbacks of the translations `τ_P`, with the action and composition laws". Those
pullbacks are evaluation at the translates of the generic point, built in
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Translation.lean`; this file is the
point they translate.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.1, II.2.

## Provenance

Not a port: none of the pinned sources introduces the generic point. The equation at the generic
point is the coordinate-ring relation `AdjoinRoot.mk_self`, pushed into the fraction field.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve.Affine R)

/-- The generic `x`-coordinate: the class of `X` in the function field. -/
noncomputable def genericX : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X))

/-- The generic `y`-coordinate: the class of `Y` in the function field. -/
noncomputable def genericY : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

/-- The generic coordinate `x` is the image of the coordinate-ring class of `X` in the function
field. -/
theorem genericX_def :
    genericX W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X)) := (rfl)

/-- The generic coordinate `y` is the image of the coordinate-ring class of `Y` in the function
field. -/
theorem genericY_def :
    genericY W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) := (rfl)

/-- The generic coordinate `x` is the image of polynomial `X` under the induced map from `R[X]`
to the function field. -/
theorem genericX_eq_algebraMap : genericX W = algebraMap R[X] W.FunctionField X := by
  rw [genericX_def, IsScalarTower.algebraMap_apply R[X] W.CoordinateRing W.FunctionField,
    AdjoinRoot.algebraMap_eq]
  (rfl)

/-- `W` base-changed to its own function field. The generic point is a point of it. -/
noncomputable abbrev functionFieldCurve : WeierstrassCurve.Affine W.FunctionField :=
  W.map (algebraMap R W.FunctionField)

/-- **Evaluating at the generic point is reduction modulo the Weierstrass relation.** A bivariate
polynomial over `R`, pushed to the function field and evaluated at `(genericX, genericY)`, is the
image of its class in the coordinate ring.

This is the workhorse: it converts any polynomial expression at the generic point into the image
of a coordinate-ring element, where the ring's own API applies. -/
theorem evalEval_genericPoint (p : R[X][Y]) :
    (p.map (mapRingHom (algebraMap R W.FunctionField))).evalEval W.genericX W.genericY =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p) := by
  conv_lhs =>
    rw [IsScalarTower.algebraMap_eq R W.CoordinateRing W.FunctionField, ← mapRingHom_comp,
      ← Polynomial.map_map]
  set g := algebraMap W.CoordinateRing W.FunctionField
  set q := Polynomial.map (mapRingHom (algebraMap R W.CoordinateRing)) p with hq
  change (q.map (mapRingHom g)).evalEval (g _) (g _) = g _
  rw [Polynomial.map_mapRingHom_evalEval]
  congr 1
  rw [hq]
  rw [← Polynomial.eval₂_eval₂RingHom_apply]
  rw [CoordinateRing.mk_C_X]
  have hinner : eval₂RingHom (algebraMap R W.CoordinateRing) (algebraMap R[X] W.CoordinateRing X) =
      algebraMap R[X] W.CoordinateRing := by
    ext x
    · simp [IsScalarTower.algebraMap_apply R R[X] W.CoordinateRing]
    · simp
  rw [hinner, ← Polynomial.aeval_def]
  exact AdjoinRoot.aeval_eq p

/-- **The generic point is a point of the curve.** `(X, Y)` satisfies the equation of `W`
base-changed to the function field, because the Weierstrass polynomial is precisely what the
coordinate ring quotients out. -/
theorem equation_genericPoint : W.functionFieldCurve.Equation W.genericX W.genericY := by
  dsimp only [Equation, functionFieldCurve]
  rw [map_polynomial, evalEval_genericPoint W W.polynomial, AdjoinRoot.mk_self, map_zero]

/-- **The two coordinate functions satisfy the Weierstrass equation of the base change to the
function field**: they are the coordinates of the generic point. -/
theorem equation_genericX_genericY :
    (W.map (algebraMap R W.FunctionField)).toAffine.Equation (genericX W) (genericY W) :=
  equation_genericPoint W

section Field

variable {F : Type*} [Field F] (W : _root_.WeierstrassCurve.Affine F)

/-- **The coordinate function `x` is transcendental over the base field.** -/
theorem transcendental_genericX : Transcendental F (genericX W) := by
  rw [genericX_eq_algebraMap]
  exact (transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective F[X] W.FunctionField)).2 (Polynomial.transcendental_X F)

/-- **The coordinate function `x` takes no constant value**, being transcendental. -/
theorem genericX_ne_algebraMap (x₁ : F) : genericX W ≠ algebraMap F W.FunctionField x₁ :=
  fun hc ↦ transcendental_genericX W (hc ▸ isAlgebraic_algebraMap _)

variable [W.IsElliptic]

/-- The generic point is nonsingular, so it is an affine point of the base-changed curve.

This is the only statement here that needs a field rather than a commutative ring: it goes
through `equation_iff_nonsingular`, which does. Everything above is stated over `[CommRing R]`,
which is all `CoordinateRing` and `FunctionField` ask for — both are `abbrev`s at that class. -/
theorem nonsingular_genericPoint :
    W.functionFieldCurve.Nonsingular W.genericX W.genericY :=
  equation_iff_nonsingular.mp (equation_genericPoint W)

/-- The generic point is nonsingular. -/
theorem nonsingular_genericX_genericY :
    (W⁄W.FunctionField).toAffine.Nonsingular (genericX W) (genericY W) :=
  nonsingular_genericPoint W

/-- **The generic point of `W`**: the tautological point of `W` with coordinates in its own
function field. -/
noncomputable def genericPoint : (W⁄W.FunctionField).toAffine.Point :=
  .some _ _ (nonsingular_genericX_genericY W)

/-- The generic point is the affine point whose coordinates are `genericX W` and `genericY W`. -/
theorem genericPoint_eq_some : genericPoint W =
    .some (genericX W) (genericY W) (nonsingular_genericX_genericY W) := (rfl)

@[simp]
theorem xCoord_genericPoint : Point.xCoord (genericPoint W) = genericX W :=
  Point.xCoord_some _

@[simp]
theorem yCoord_genericPoint : Point.yCoord (genericPoint W) = genericY W :=
  Point.yCoord_some _

end Field

end WeierstrassCurve.Affine

end
