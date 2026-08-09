/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The point map induced by a ring homomorphism

Mathlib's `WeierstrassCurve.Affine.Point.map` moves the points of a *fixed* curve between two
**field** extensions of a base, along an `AlgHom` in a scalar tower. This file supplies the other
functoriality: an injective ring homomorphism `f : R →+* S` carries the points of `W` over `R` to
the points of the curve `W.map f` over `S`, with no fields and no tower involved.

## Main definitions and results

* `TauCeti.WeierstrassCurve.Affine.Point.mapRingHom`: the map `W.Point → (W.map f).Point`, over
  arbitrary commutative rings.
* `TauCeti.WeierstrassCurve.Affine.Point.mapRingHomAddMonoidHom`: over a field, it is additive, so
  it packages as an `AddMonoidHom`; `mapRingHom_zsmul` is the resulting compatibility with `ℤ`
  scalars.

The definition needs only injectivity, since that is what `Affine.map_nonsingular` needs to carry
nonsingularity across. Additivity is stated over a field because that is where Mathlib gives
`W.Point` its group law.

This supports the Hasse strand of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 3: the Silverman
V.1 route counts `#E(𝔽_q)` as the fixed points of Frobenius, which means transporting points along
the `q`-power ring homomorphism and knowing that transport respects the group law and `ℤ`-multiples.
The roadmap's §"What Mathlib already has (consume)" lists `Affine.Point` and its `AddCommGroup` as
consumed infrastructure whose "infrastructure is load-bearing API here, not an implementation
detail"; this is a complement to that API, not a reimplementation of it.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/EC/AffinePointMap.lean`, declarations
`map`, `map_zero`, `map_some`, `map_add`, `map_neg`, `mapAddMonoidHom` and `map_zsmul`.

Changes from the source. The names carry a `RingHom` suffix, Mathlib having taken `Point.map` for
the `AlgHom` version since. The source's `map_add` is a chain of `change` steps naming the
constructor arguments in full; here the two degenerate cases go through `Point.zero_add`/`add_zero`
after a single `cases`, and the `Y`-cancellation branch is derived from
`Affine.map_negY` rather than restated.
-/

public section

open WeierstrassCurve

namespace TauCeti

namespace WeierstrassCurve.Affine.Point

variable {R S : Type*} [CommRing R] [CommRing S] {W : _root_.WeierstrassCurve R} (f : R →+* S)
  (hf : Function.Injective f)

/-- **The points of `W` map to the points of `W.map f` along an injective ring homomorphism.**
Nonsingularity transports by Mathlib's `Affine.map_nonsingular`, which is what injectivity is
for. -/
noncomputable def mapRingHom : W.toAffine.Point → (W.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((Affine.map_nonsingular W.toAffine hf x y).mpr h)

@[simp]
lemma mapRingHom_zero : mapRingHom f hf (0 : W.toAffine.Point) = 0 := by
  change mapRingHom f hf .zero = .zero
  simp [mapRingHom]

@[simp]
lemma mapRingHom_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapRingHom f hf (.some x y h)
      = .some (f x) (f y) ((Affine.map_nonsingular W.toAffine hf x y).mpr h) := by
  simp [mapRingHom]

end WeierstrassCurve.Affine.Point

namespace WeierstrassCurve.Affine.Point

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  {W : _root_.WeierstrassCurve F} (f : F →+* K)

/-- **The point map is additive**: over a field it commutes with the group law. -/
lemma mapRingHom_add (P Q : W.toAffine.Point) :
    mapRingHom f f.injective (P + Q)
      = mapRingHom f f.injective P + mapRingHom f f.injective Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · change mapRingHom f f.injective ((0 : W.toAffine.Point) + Q)
      = mapRingHom f f.injective (0 : W.toAffine.Point) + mapRingHom f f.injective Q
    rw [zero_add, mapRingHom_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · change mapRingHom f f.injective (_ + (0 : W.toAffine.Point))
      = mapRingHom f f.injective _ + mapRingHom f f.injective (0 : W.toAffine.Point)
    rw [add_zero, mapRingHom_zero, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    have hy' : f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂) := by rw [hy, Affine.map_negY]
    rw [Affine.Point.add_of_Y_eq hx hy, mapRingHom_zero, mapRingHom_some, mapRingHom_some,
      Affine.Point.add_of_Y_eq (congrArg f hx) hy']
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hfx, hfy⟩
      exact hxy ⟨f.injective hfx, f.injective (by rwa [Affine.map_negY] at hfy)⟩
    rw [Affine.Point.add_some hxy, mapRingHom_some, mapRingHom_some, mapRingHom_some,
      Affine.Point.add_some hxy']
    simp only [Affine.map_slope, Affine.map_addX, Affine.map_addY]

omit [DecidableEq F] [DecidableEq K] in
/-- **The point map preserves negation.** Unlike additivity this needs no decidability, negation
being defined without a case split. -/
lemma mapRingHom_neg (P : W.toAffine.Point) :
    mapRingHom f f.injective (-P) = -mapRingHom f f.injective P := by
  rcases P with _ | ⟨x, y, h⟩
  · change mapRingHom f f.injective (-(0 : W.toAffine.Point))
      = -mapRingHom f f.injective (0 : W.toAffine.Point)
    simp
  · rw [Affine.Point.neg_some, mapRingHom_some, mapRingHom_some, Affine.Point.neg_some]
    simp only [Affine.map_negY]

variable (W) in
/-- The point map packaged as an `AddMonoidHom`. -/
noncomputable def mapRingHomAddMonoidHom : W.toAffine.Point →+ (W.map f).toAffine.Point where
  toFun := mapRingHom f f.injective
  map_zero' := mapRingHom_zero f f.injective
  map_add' := mapRingHom_add f

@[simp]
lemma mapRingHomAddMonoidHom_apply (P : W.toAffine.Point) :
    mapRingHomAddMonoidHom W f P = mapRingHom f f.injective P := by
  simp [mapRingHomAddMonoidHom]

/-- **The point map commutes with `ℤ`-multiples**, which is what a multiplication-by-`n` argument
transported along `f` needs. -/
lemma mapRingHom_zsmul (n : ℤ) (P : W.toAffine.Point) :
    mapRingHom f f.injective (n • P) = n • mapRingHom f f.injective P :=
  (mapRingHomAddMonoidHom W f).map_zsmul n P

end WeierstrassCurve.Affine.Point

end TauCeti

end
