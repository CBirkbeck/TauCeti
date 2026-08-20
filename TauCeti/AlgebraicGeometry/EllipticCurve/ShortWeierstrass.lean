/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The short Weierstrass curve `y² = x³ + Ax + B`

Mathlib carries short Weierstrass form as a *predicate*, `WeierstrassCurve.IsShortNF`, asserting
`a₁ = a₂ = a₃ = 0` of a curve one already has, together with the invariants that follow from it
(`Δ_of_isShortNF`, `j_of_isShortNF`, and the `b`- and `c`-families). What it does not carry is the
*constructor*: the curve built from a chosen pair of coefficients. Statements phrased over an
explicit `y² = x³ + Ax + B` — the classical form of the Nagell–Lutz theorem among them — need that
constructor, so it is supplied here, with the `IsShortNF` instance that connects it to everything
Mathlib already proves.

Only the two coefficient values are stated as lemmas. Every other fact about `shortCurve` —
`a₁ = a₂ = a₃ = 0`, the `b`- and `c`-invariants, `Δ` and `j` — is inherited through the instance
rather than restated, so `Δ_shortCurve` below is `Mathlib`'s `Δ_of_isShortNF` read at these
coefficients.

## Main definitions

* `TauCeti.WeierstrassCurve.shortCurve`: the curve `y² = x³ + Ax + B` over a commutative ring.

## Main results

* `TauCeti.WeierstrassCurve.instIsShortNFShortCurve`: it is in short normal form, which is what
  makes Mathlib's `*_of_isShortNF` family apply to it.
* `TauCeti.WeierstrassCurve.map_shortCurve`: short form is preserved by a ring hom, and the
  coefficients transport. Mathlib has no `IsShortNF`-under-`map` instance, so this is what lets a
  curve over `ℤ` be base changed to `ℚ` and stay recognisably short.
* `TauCeti.WeierstrassCurve.Δ_shortCurve`: the classical discriminant `-16(4A³ + 27B²)`.
* `TauCeti.WeierstrassCurve.equation_shortCurve_iff`: a point lies on it exactly when
  `y² = x³ + Ax + B`.

This is a prerequisite of the Nagell–Lutz milestone of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz",
whose classical statement is about this curve and its discriminant.

## Provenance

Adapted from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
`LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean`: `shortCurveZ` (`:30`), `shortCurveQ` (`:34`),
`shortCurveQ_equation_iff` (`:58`) and `shortCurveZ_delta` (`:63`).

Three departures. The source fixes `ℤ` and `ℚ`; here the construction is over an arbitrary
commutative ring and `map_shortCurve` relates the two, so the `ℤ → ℚ` pair of the classical
statement is one definition and a base change rather than two definitions. The source's ten
`@[simp]` coefficient lemmas — `shortCurve{Z,Q}_a₁` through `_a₆` — are not ported: eight of them
are `a₁ = a₂ = a₃ = 0` twice over, which the `IsShortNF` instance supplies through Mathlib's
`a₁_of_isShortNF`, `a₂_of_isShortNF` and `a₃_of_isShortNF`. And `shortCurveZ_delta` is not proved
from `simp [Δ, b₂, b₄, b₆, b₈]; ring1` as the source does but read off Mathlib's
`Δ_of_isShortNF`, which states exactly `-16(4a₄³ + 27a₆²)`.
-/

public section

namespace TauCeti

namespace WeierstrassCurve

open _root_.WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] (A B : R)

/-- The short Weierstrass curve `y² = x³ + Ax + B`. -/
def shortCurve : _root_.WeierstrassCurve R where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B

@[simp] lemma shortCurve_a₄ : (shortCurve A B).a₄ = A := (rfl)

@[simp] lemma shortCurve_a₆ : (shortCurve A B).a₆ = B := (rfl)

/-- `shortCurve A B` is in short normal form. This instance is the point of the definition: it
hands the curve to Mathlib's whole `*_of_isShortNF` family, so the vanishing coefficients and
every invariant come for free rather than being restated here. -/
instance : (shortCurve A B).IsShortNF := ⟨(rfl), (rfl), (rfl)⟩

/-- A ring hom carries `shortCurve` to `shortCurve` on the images of the coefficients. Mathlib has
no instance propagating `IsShortNF` along `map`, so this is what keeps a base change — `ℤ → ℚ` in
the classical Nagell–Lutz statement — recognisably in short form. -/
@[simp] lemma map_shortCurve (f : R →+* S) : (shortCurve A B).map f = shortCurve (f A) (f B) := by
  ext <;> simp [shortCurve, _root_.WeierstrassCurve.map]

/-- The discriminant of `y² = x³ + Ax + B` is `-16(4A³ + 27B²)`, Mathlib's `Δ_of_isShortNF` read
at these coefficients. -/
lemma Δ_shortCurve : (shortCurve A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simpa using (shortCurve A B).Δ_of_isShortNF

/-- A point lies on `y² = x³ + Ax + B` exactly when it satisfies that equation. -/
lemma equation_shortCurve_iff (x y : R) :
    (shortCurve A B).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + A * x + B := by
  rw [Affine.equation_iff]
  simp [shortCurve]

end WeierstrassCurve

end TauCeti
