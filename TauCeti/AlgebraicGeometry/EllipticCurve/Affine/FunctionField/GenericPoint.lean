/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing

/-!
# The generic point of an affine Weierstrass curve

The coordinate ring `W.CoordinateRing` is `F[X][Y]` modulo the Weierstrass relation, so the
classes of `X` and `Y` in the function field are a pair satisfying that relation over
`W.FunctionField`. They are the *generic point*: a point of `W` base-changed to its own function
field, and the universal one, in that a statement about it specialises to every point of `W`.

The two facts worth having are `equation_genericPoint`, that the pair really is a point, and
`evalEval_genericPoint`, that evaluating a bivariate polynomial there is the same as reducing it
modulo the Weierstrass relation. The second is what makes the generic point usable: it turns any
polynomial expression evaluated at `(X, Y)` into a coordinate-ring element, where that ring's
own API applies.

## Main definitions

* `WeierstrassCurve.Affine.genericX`, `WeierstrassCurve.Affine.genericY`: the coordinates.
* `WeierstrassCurve.Affine.functionFieldCurve`: `W` base-changed to `W.FunctionField`.

## Main results

* `WeierstrassCurve.Affine.equation_genericPoint`: the generic point satisfies the equation.
* `WeierstrassCurve.Affine.nonsingular_genericPoint`: and is nonsingular, on an elliptic curve.
* `WeierstrassCurve.Affine.evalEval_genericPoint`: evaluation there is reduction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.1.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- The generic `x`-coordinate: the class of `X` in the function field. -/
noncomputable def genericX : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (algebraMap F[X] W.CoordinateRing X)

/-- The generic `y`-coordinate: the class of `Y` in the function field. -/
noncomputable def genericY : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.root W.polynomial)

/-- **The defining equation of `genericX`.** Under the module system a `def`'s body is sealed
across the module boundary even inside a `public section`, so a downstream file can unfold it by
neither `rw` nor `simp only`. This lemma and `genericY_def` are how the two are computed with
from outside. -/
theorem genericX_def : W.genericX =
    algebraMap W.CoordinateRing W.FunctionField (algebraMap F[X] W.CoordinateRing X) := (rfl)

/-- **The defining equation of `genericY`.** -/
theorem genericY_def : W.genericY =
    algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.root W.polynomial) := (rfl)

/-- `W` base-changed to its own function field. The generic point is a point of it. -/
noncomputable abbrev functionFieldCurve : WeierstrassCurve.Affine W.FunctionField :=
  W.map (algebraMap F W.FunctionField)

/-- The composite `F → W.FunctionField` factors through the coordinate ring. Used to turn
statements about the base-changed curve into statements about images under
`algebraMap W.CoordinateRing W.FunctionField`. -/
theorem algebraMap_functionField_eq_comp :
    (algebraMap F W.FunctionField : F →+* W.FunctionField) =
      (algebraMap W.CoordinateRing W.FunctionField).comp (algebraMap F W.CoordinateRing) :=
  (IsScalarTower.algebraMap_eq F W.CoordinateRing W.FunctionField).symm

/-- **Evaluating at the generic point is reduction modulo the Weierstrass relation.** A bivariate
polynomial over `F`, pushed to the function field and evaluated at `(genericX, genericY)`, is the
image of its class in the coordinate ring.

This is the workhorse: it converts any polynomial expression at the generic point into the image
of a coordinate-ring element, where the ring's own API applies. -/
theorem evalEval_genericPoint (p : F[X][Y]) :
    (p.map (mapRingHom (algebraMap F W.FunctionField))).evalEval W.genericX W.genericY =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p) := by
  conv_lhs =>
    rw [algebraMap_functionField_eq_comp W, ← mapRingHom_comp, ← Polynomial.map_map]
  set g := algebraMap W.CoordinateRing W.FunctionField
  set q := Polynomial.map (mapRingHom (algebraMap F W.CoordinateRing)) p with hq
  -- `genericX` and `genericY` are already of the form `g _`; say so, or the rewrite below
  -- cannot see its own pattern `evalEval (g _) (g _) (map (mapRingHom g) _)`.
  change (q.map (mapRingHom g)).evalEval (g _) (g _) = g _
  rw [Polynomial.map_mapRingHom_evalEval]
  congr 1
  rw [hq]
  rw [← Polynomial.eval₂_eval₂RingHom_apply]
  have hinner : eval₂RingHom (algebraMap F W.CoordinateRing) (algebraMap F[X] W.CoordinateRing X) =
      algebraMap F[X] W.CoordinateRing := by
    ext x
    · simp [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing]
    · simp
  rw [hinner, ← Polynomial.aeval_def]
  exact AdjoinRoot.aeval_eq p

/-- **The generic point is a point of the curve.** `(X, Y)` satisfies the equation of `W`
base-changed to the function field, because the Weierstrass polynomial is precisely what the
coordinate ring quotients out. -/
theorem equation_genericPoint : W.functionFieldCurve.Equation W.genericX W.genericY := by
  dsimp only [Equation, functionFieldCurve]
  rw [map_polynomial, evalEval_genericPoint W W.polynomial, AdjoinRoot.mk_self, map_zero]

/-- The generic point is nonsingular, so it is an affine point of the base-changed curve. -/
theorem nonsingular_genericPoint [W.IsElliptic] :
    W.functionFieldCurve.Nonsingular W.genericX W.genericY :=
  equation_iff_nonsingular.mp (equation_genericPoint W)

end WeierstrassCurve.Affine
