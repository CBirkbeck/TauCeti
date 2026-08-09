/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# The function field of a Weierstrass curve has degree two over `K(x)`

Mathlib gives the coordinate ring `R[W]` a power basis `{1, Y}` over `R[X]`, so it is free of rank
two, and defines the function field `R(W)` as its fraction field. It says nothing about `R(W)` as
an extension of `R(x) = FractionRing R[X]` — indeed it provides no algebra structure for that pair,
so the statement cannot even be written against Mathlib alone. This file exports the structure and
proves the degree.

## Main results

* `WeierstrassCurve.Affine.moduleFinite_coordinateRing` and `isIntegral_coordinateRing`: the
  coordinate ring is module-finite and integral over `R[X]`, over any commutative ring.
* `WeierstrassCurve.Affine.finrank_coordinateRing`: it has rank two, under
  `[StrongRankCondition R[X]]` — the hypothesis `Module.finrank` actually needs, automatic over a
  domain.
* `WeierstrassCurve.Affine.algebraFractionRingFunctionField` and
  `isScalarTowerFractionRingFunctionField`: the `R(x)`-algebra structure on `R(W)` and the tower
  `R[X] ⊆ R(x) ⊆ R(W)`, over any integral domain.
* `WeierstrassCurve.Affine.finrank_functionField`: `[R(W) : R(x)] = 2`.

The base change itself is Mathlib's `Algebra.IsAlgebraic.isBaseChange_of_isFractionRing`; what is
missing from Mathlib is the `R(x)`-algebra structure on `R(W)` that lets the statement be written
at all, and the instances feeding that generic theorem. Mathlib supplies the algebra as
`FractionRing.liftAlgebra` but deliberately keeps it out of the instance graph, since for a general
target it collides with the identity structure on `FractionRing R[X]` itself; `R(W)` is a quadratic
extension of `R(x)`, so that collision cannot arise here and the instance is exported rather than
activated locally.

## Roadmap

The Hasse strand of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 3. The degree of the Frobenius
isogeny is computed from the tower `K(W) ⊇ K(x) ⊇ K(x^q)`, where the outer degrees are this `2` and
the inner degree is `q`; the roadmap calls the Frobenius "the key input to Layer 3". It is also
Layer 0 infrastructure: the roadmap's §"What Mathlib already has (consume)" lists
`Affine.FunctionField` as consumed, and this is a complement to that API rather than a
reimplementation of it.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/FrobeniusIsogeny.lean`, declarations
`finrank_coordinateRing_eq_two`, `isBaseChange_coordToFunc` and `finrank_functionField_eq_two`,
together with the algebra and localization instances they rest on.

Changes from the source. Those instances are stated there inside a file that also builds the
Frobenius isogeny; here they are separated out, since the degree of `R(W)` over `R(x)` is a fact
about the curve and not about any isogeny. The source states everything over a field; here the
coordinate-ring half is over an arbitrary commutative ring and the function-field half over an
integral domain, which is all either argument uses. The source's `FaithfulSMul K[X] K[W]` instance
and its `algebraMap_poly_injective` are dropped: Mathlib now supplies both, the first as an
instance in `Affine/Point.lean` and the second as `FaithfulSMul.algebraMap_injective`.
-/

public section

open Polynomial

open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)

/-- The coordinate ring is module-finite over `R[X]`, on Mathlib's power basis `{1, Y}`. -/
instance moduleFinite_coordinateRing : Module.Finite R[X] W.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W)

/-- The coordinate ring is integral over `R[X]`, being module-finite. -/
instance isIntegral_coordinateRing : Algebra.IsIntegral R[X] W.CoordinateRing :=
  Algebra.IsIntegral.of_finite R[X] W.CoordinateRing

/-- **The coordinate ring is free of rank two over `R[X]`**, whenever ranks over `R[X]` are well
behaved — which is what `StrongRankCondition` asks, and is automatic over a field. -/
lemma finrank_coordinateRing [StrongRankCondition R[X]] :
    Module.finrank R[X] W.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (CoordinateRing.basis W)).trans (Fintype.card_fin 2)

end CommRing

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve.Affine R)

/-- **The rational function field `R(x)` acts on the function field `R(W)`.** Mathlib keeps
`FractionRing.liftAlgebra` out of the instance graph because it collides with the identity
structure when the target *is* `FractionRing R[X]`; `R(W)` is a quadratic extension of `R(x)`, so
that collision cannot arise for this pair and the instance is exported. -/
noncomputable instance algebraFractionRingFunctionField :
    Algebra (FractionRing R[X]) W.FunctionField :=
  FractionRing.liftAlgebra R[X] W.FunctionField

/-- `R(x)` sits between `R[X]` and `R(W)`. -/
instance isScalarTowerFractionRingFunctionField :
    IsScalarTower R[X] (FractionRing R[X]) W.FunctionField :=
  FractionRing.isScalarTower_liftAlgebra R[X] W.FunctionField

/-- **The function field of a Weierstrass curve is a quadratic extension of `R(x)`.** The function
field is the base change of the coordinate ring along `R[X] → R(x)`, by Mathlib's
`Algebra.IsAlgebraic.isBaseChange_of_isFractionRing`, and the coordinate ring has rank two. -/
theorem finrank_functionField :
    Module.finrank (FractionRing R[X]) W.FunctionField = 2 := by
  rw [(Algebra.IsAlgebraic.isBaseChange_of_isFractionRing R[X] W.CoordinateRing
    (FractionRing R[X]) W.FunctionField).finrank_eq, finrank_coordinateRing]

end Domain

end WeierstrassCurve.Affine

end
