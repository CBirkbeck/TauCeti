/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The affine coordinates of a point

Mathlib's `WeierstrassCurve.Affine.Point` is an inductive type with a constructor for the point at
infinity and a constructor `Point.some x y h` carrying the two coordinates of an affine point. Some
constructions have to read those coordinates off a point that is only *known* to be nonzero — the
translation action on the function field is the motivating example — and pattern matching inside a
definition makes every downstream statement a case split. This file provides the two total
accessors instead, junk-valued at the point at infinity, together with the fact that the pair they
return satisfies `Nonsingular` as soon as the point is nonzero.

## Main definitions

* `TauCeti.WeierstrassCurve.Affine.Point.xCoord` and
  `TauCeti.WeierstrassCurve.Affine.Point.yCoord`: the two coordinates, `0` at the point at
  infinity.

## Main results

* `TauCeti.WeierstrassCurve.Affine.Point.nonsingular_coords` and
  `TauCeti.WeierstrassCurve.Affine.Point.some_coords`: a nonzero point is `Point.some` of its two
  coordinates, which satisfy `Nonsingular`.
* `TauCeti.WeierstrassCurve.Affine.Point.map_xCoord` and
  `TauCeti.WeierstrassCurve.Affine.Point.map_yCoord`: both accessors commute with Mathlib's
  `Point.map` along an algebra homomorphism, the point at infinity included — the form the
  translation action consumes.

The junk value `0` is deliberate and harmless: `xCoord_zero` records it, and every statement that
depends on the value assumes `P ≠ 0`. Nothing here needs a field, an elliptic curve or the group
law; the two `map` lemmas need the field hypotheses only because Mathlib's `Point.map` does.

This is infrastructure for `TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0.5**, whose third
milestone asks for "function-field pullbacks of the translations `τ_P`, with the action and
composition laws": the pullback of `τ_P` is evaluation at the coordinates of a translate of the
generic point, and those coordinates are exactly what these accessors name.

## Provenance

Not a port: Mathlib carries only `Point.xRep`, the projective representative of the
`x`-coordinate map to `ℙ¹`, which is a different object (it is constant on `±P` by design and
records no `y`).
-/

public section

open WeierstrassCurve

namespace TauCeti

namespace WeierstrassCurve.Affine.Point

variable {R : Type*} [CommRing R] {W : _root_.WeierstrassCurve.Affine R}

/-- The `x`-coordinate of a point, taken to be `0` at the point at infinity. -/
def xCoord : W.Point → R
  | 0 => 0
  | .some x _ _ => x

/-- The `y`-coordinate of a point, taken to be `0` at the point at infinity. -/
def yCoord : W.Point → R
  | 0 => 0
  | .some _ y _ => y

@[simp]
theorem xCoord_zero : xCoord (0 : W.Point) = 0 := (rfl)

@[simp]
theorem yCoord_zero : yCoord (0 : W.Point) = 0 := (rfl)

@[simp]
theorem xCoord_some {x y : R} (h : W.Nonsingular x y) : xCoord (.some x y h) = x := (rfl)

@[simp]
theorem yCoord_some {x y : R} (h : W.Nonsingular x y) : yCoord (.some x y h) = y := (rfl)

/-- **The coordinates of a nonzero point are a nonsingular solution of the equation.** -/
theorem nonsingular_coords {P : W.Point} (hP : P ≠ 0) : W.Nonsingular (xCoord P) (yCoord P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact h

/-- **A nonzero point is `Point.some` of its two coordinates.** -/
theorem some_coords {P : W.Point} (hP : P ≠ 0) :
    _root_.WeierstrassCurve.Affine.Point.some (xCoord P) (yCoord P)
      (nonsingular_coords hP) = P := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => (rfl)

@[simp]
theorem xCoord_neg (P : W.Point) : xCoord (-P) = xCoord P := by
  cases P <;> (rfl)

variable {S F K : Type*} [CommRing S] [Field F] [Field K] [Algebra R S] [Algebra R F] [Algebra S F]
  [IsScalarTower R S F] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  [DecidableEq F] [DecidableEq K]

/-- **The `x`-coordinate commutes with `Point.map`.** The point at infinity needs no exception:
both sides are `0` there. -/
@[simp]
theorem map_xCoord (f : F →ₐ[S] K) (P : (W⁄F).toAffine.Point) :
    xCoord (_root_.WeierstrassCurve.Affine.Point.map f P)
      = f (xCoord P) := by
  cases P with
  | zero =>
    rw [← _root_.WeierstrassCurve.Affine.Point.zero_def, map_zero, xCoord_zero, xCoord_zero,
      map_zero]
  | some x y h => (rfl)

/-- **The `y`-coordinate commutes with `Point.map`.** -/
@[simp]
theorem map_yCoord (f : F →ₐ[S] K) (P : (W⁄F).toAffine.Point) :
    yCoord (_root_.WeierstrassCurve.Affine.Point.map f P)
      = f (yCoord P) := by
  cases P with
  | zero =>
    rw [← _root_.WeierstrassCurve.Affine.Point.zero_def, map_zero, yCoord_zero, yCoord_zero,
      map_zero]
  | some x y h => (rfl)

end WeierstrassCurve.Affine.Point

end TauCeti

end
