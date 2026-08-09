/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The function field of a Weierstrass curve has degree two over `K(x)`

Mathlib gives the coordinate ring `K[W]` a power basis `{1, Y}` over `K[X]`, so it is free of rank
two, and defines the function field `K(W)` as its fraction field. It says nothing about `K(W)` as
an extension of `K(x) = FractionRing K[X]` — indeed it provides no algebra structure for that pair,
so the statement cannot even be written against Mathlib alone. This file supplies the structure and
the degree.

## Main results

* `WeierstrassCurve.Affine.moduleFinite_coordinateRing` and `isIntegral_coordinateRing`: the
  coordinate ring is module-finite and integral over `R[X]`, over any commutative ring.
* `WeierstrassCurve.Affine.finrank_coordinateRing`: it has rank two. Stated over a field, since
  `Module.finrank` needs `StrongRankCondition K[X]`, which `R[X]` inherits only from `R`.
* `WeierstrassCurve.Affine.finrank_functionField`: `[K(W) : K(x)] = 2`.

The base change itself is Mathlib's `Algebra.IsAlgebraic.isBaseChange_of_isFractionRing`; what is
missing from Mathlib is the `K(x)`-algebra structure on `K(W)` that lets the statement be written
at all, and the instances feeding that generic theorem.

## Roadmap

The Hasse strand of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 3. The degree of the Frobenius
isogeny is computed from the tower `K(W) ⊇ K(x) ⊇ K(x^q)`, where the outer degrees are this `2` and
the inner degree is `q`; the roadmap calls the Frobenius "the key input to Layer 3". It is also
Layer 0 infrastructure: the roadmap's §"What Mathlib already has (consume)" lists
`Affine.FunctionField` as consumed, and this is a complement to that API rather than a
reimplementation of it.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/FrobeniusIsogeny.lean`, declarations
`finrank_coordinateRing_eq_two`, `isBaseChange_coordToFunc` and `finrank_functionField_eq_two`,
together with the algebra and localization instances they rest on.

Changes from the source. Those instances are stated there inside a file that also builds the
Frobenius isogeny; here they are separated out, since the degree of `K(W)` over `K(x)` is a fact
about the curve and not about any isogeny. The source's `FaithfulSMul K[X] K[W]` instance and its
`algebraMap_poly_injective` are dropped: Mathlib now supplies both, the first as an instance in
`Affine/Point.lean` and the second as `FaithfulSMul.algebraMap_injective`.
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

end CommRing

section Field

variable {K : Type*} [Field K] (W : WeierstrassCurve.Affine K)

/-- **The coordinate ring is free of rank two over `K[X]`.** Stated over a field rather than an
arbitrary commutative ring: `Module.finrank` needs `StrongRankCondition K[X]`, which `R[X]` has
only when `R` does. -/
lemma finrank_coordinateRing : Module.finrank K[X] W.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (CoordinateRing.basis W)).trans (Fintype.card_fin 2)

/-- `K(x) = FractionRing K[X]` acts on the function field, through the coordinate ring. -/
noncomputable instance algebra_fractionRing_functionField :
    Algebra (FractionRing K[X]) W.FunctionField :=
  FractionRing.liftAlgebra K[X] W.FunctionField

/-- The action of `K(x)` on the function field extends the action of `K[X]`. -/
noncomputable instance isScalarTower_fractionRing_functionField :
    IsScalarTower K[X] (FractionRing K[X]) W.FunctionField :=
  FractionRing.isScalarTower_liftAlgebra K[X] W.FunctionField

/-- **The function field of a Weierstrass curve is a quadratic extension of `K(x)`.** The function
field is the base change of the coordinate ring along `K[X] → K(x)`, by Mathlib's
`Algebra.IsAlgebraic.isBaseChange_of_isFractionRing`, and the coordinate ring has rank two. -/
theorem finrank_functionField :
    Module.finrank (FractionRing K[X]) W.FunctionField = 2 := by
  rw [(Algebra.IsAlgebraic.isBaseChange_of_isFractionRing K[X] W.CoordinateRing
    (FractionRing K[X]) W.FunctionField).finrank_eq, finrank_coordinateRing]

end Field

end WeierstrassCurve.Affine

end
