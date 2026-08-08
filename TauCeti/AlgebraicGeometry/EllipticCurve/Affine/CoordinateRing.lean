/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Faithfulness of the coordinate ring, and equality of affine points

Two injectivity facts about Mathlib's affine API for a Weierstrass curve, both absent from the
pinned Mathlib.

The coordinate ring `R[X][Y] ⧸ ⟨polynomial⟩` contains `R[X]` faithfully: quotienting by the
Weierstrass polynomial kills nothing in `X` alone, because the free `R[X]`-basis `{1, Y}` of the
coordinate ring has `1` as one of its members. Consequently the base ring `R` embeds too.

Separately, `Affine.Point.some` is injective in its coordinates, so two nonsingular points are
equal exactly when their coordinates agree.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.algebraMap_poly_injective`
* `WeierstrassCurve.Affine.CoordinateRing.algebraMap_injective'`
* `WeierstrassCurve.Affine.Point.some_eq_some_iff`

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Auxiliary/Universal.lean`, declarations `algebraMap_poly_injective`,
`algebraMap_injective'` and `some_eq_some_iff` (© Junyan Xu). Only these three are taken: the rest
of that file constructs the universal elliptic curve over `ℤ[A₁,…,A₆]`, which is a large
mathlib-track development rather than a leaf, and is left alone.

The source guards the first proof with `set_option backward.isDefEq.respectTransparency false`,
which this repository forbids; it is not needed here.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : WeierstrassCurve.Affine R}

namespace CoordinateRing

/-- The coordinate ring contains `R[X]` faithfully.

A polynomial in `X` alone that dies in the quotient must vanish, since `1` is a member of the free
`R[X]`-basis `{1, Y}` of the coordinate ring. -/
theorem algebraMap_poly_injective : Function.Injective (algebraMap R[X] W'.CoordinateRing) :=
  (injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <|
    smul_basis_eq_zero (W' := W') (q := 0) <| by
      rwa [Algebra.smul_def, mul_one, zero_smul, add_zero]

/-- The coordinate ring contains the base ring faithfully, by composing with `Polynomial.C`. -/
theorem algebraMap_injective' : Function.Injective (algebraMap R W'.CoordinateRing) :=
  algebraMap_poly_injective.comp C_injective

end CoordinateRing

namespace Point

/-- Two nonsingular affine points are equal exactly when their coordinates agree. -/
theorem some_eq_some_iff {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Nonsingular x₁ y₁)
    (h₂ : W'.Nonsingular x₂ y₂) : some x₁ y₁ h₁ = some x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂ :=
  ⟨by rintro (_ | _); trivial, by rintro ⟨rfl, rfl⟩; rfl⟩

end Point

end WeierstrassCurve.Affine
