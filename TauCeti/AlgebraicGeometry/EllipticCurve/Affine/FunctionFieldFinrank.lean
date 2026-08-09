/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# The function field of a Weierstrass curve has degree two over `K(x)`

Mathlib gives the coordinate ring `K[W]` a power basis `{1, Y}` over `K[X]`, so it is free of rank
two, and defines the function field `K(W)` as its fraction field. It says nothing about `K(W)` as
an extension of `K(x) = FractionRing K[X]` — indeed it provides no algebra structure for that pair,
so the statement cannot even be written against Mathlib alone. This file supplies the structure and
the degree.

## Main results

* `WeierstrassCurve.Affine.finrank_coordinateRing`: the coordinate ring is free of rank two over
  `K[X]`.
* `WeierstrassCurve.Affine.isBaseChange_functionField`: `K(W)` is the base change of `K[W]` along
  `K[X] → K(x)`.
* `WeierstrassCurve.Affine.finrank_functionField`: `[K(W) : K(x)] = 2`.

This is Silverman II.2: the function field of a Weierstrass curve is a quadratic extension of the
rational function field in `x`, the nontrivial element of the extension being `y`.

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

variable {K : Type*} [Field K] (W : WeierstrassCurve.Affine K)

/-- **The coordinate ring is free of rank two over `K[X]`**, on Mathlib's power basis `{1, Y}`. -/
lemma finrank_coordinateRing : Module.finrank K[X] W.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (CoordinateRing.basis W)).trans (Fintype.card_fin 2)

/-- `K(x) = FractionRing K[X]` acts on the function field, through the coordinate ring. -/
noncomputable instance algebraFractionRingFunctionField :
    Algebra (FractionRing K[X]) W.FunctionField :=
  FractionRing.liftAlgebra K[X] W.FunctionField

noncomputable instance isScalarTowerFractionRingFunctionField :
    IsScalarTower K[X] (FractionRing K[X]) W.FunctionField :=
  FractionRing.isScalarTower_liftAlgebra K[X] W.FunctionField

instance moduleFiniteCoordinateRing : Module.Finite K[X] W.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W)

instance isIntegralCoordinateRing : Algebra.IsIntegral K[X] W.CoordinateRing :=
  Algebra.IsIntegral.of_finite K[X] W.CoordinateRing

private noncomputable instance isLocalizationFunctionField : IsLocalization
    (Algebra.algebraMapSubmonoid W.CoordinateRing K[X]⁰) W.FunctionField := by
  have : Algebra.IsAlgebraic K[X] W.CoordinateRing := Algebra.IsIntegral.isAlgebraic
  have := (FaithfulSMul.algebraMap_injective K[X] W.CoordinateRing).noZeroDivisors _
    (map_zero _) (map_mul _)
  exact (IsLocalization.iff_of_le_of_exists_dvd _ (nonZeroDivisors W.CoordinateRing)
    (map_le_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective K[X] W.CoordinateRing) le_rfl)
    fun s hs ↦
      have ⟨r, ne, eq⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := K[X]) s).exists_nonzero_dvd hs
      ⟨_, ⟨r, mem_nonZeroDivisors_of_ne_zero ne, rfl⟩, eq⟩).mpr inferInstance

private noncomputable instance isLocalizedModuleCoordToFunc : IsLocalizedModule K[X]⁰
    (IsScalarTower.toAlgHom K[X] W.CoordinateRing W.FunctionField).toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr inferInstance

/-- **The function field is the base change of the coordinate ring along `K[X] → K(x)`.** -/
theorem isBaseChange_functionField :
    IsBaseChange (FractionRing K[X])
      (IsScalarTower.toAlgHom K[X] W.CoordinateRing W.FunctionField).toLinearMap :=
  (isLocalizedModule_iff_isBaseChange K[X]⁰ ..).mp inferInstance

/-- **The function field of a Weierstrass curve is a quadratic extension of `K(x)`.** -/
theorem finrank_functionField :
    Module.finrank (FractionRing K[X]) W.FunctionField = 2 := by
  rw [(isBaseChange_functionField W).finrank_eq, finrank_coordinateRing]

end WeierstrassCurve.Affine

end
