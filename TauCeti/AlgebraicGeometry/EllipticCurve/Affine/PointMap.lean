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
* `TauCeti.WeierstrassCurve.Affine.Point.mapRingHom_neg`, `mapRingHom_id`,
  `mapRingHom_mapRingHom` and `mapRingHom_injective`: the functorial API, over arbitrary
  commutative rings, mirroring Mathlib's
  `Affine.Point.map_id`, `map_map` and `map_injective` for the `AlgHom` version. The identity and
  composition laws transport their codomains along Mathlib's `WeierstrassCurve.map_id` and
  `map_map`.

* `TauCeti.WeierstrassCurve.Affine.Point.mapRingHom_eq_map`: over a field, for **any** ring
  homomorphism `f` — in particular a `q`-power Frobenius, which is not an ambient `algebraMap` —
  the transport *is* Mathlib's `Affine.Point.map` once `K` carries the `F`-algebra structure `f`
  induces.
* `TauCeti.WeierstrassCurve.Affine.Point.mapRingHom_add` and `mapRingHom_zsmul`: compatibility
  with the group law and with `ℤ`-multiples, each a one-line consequence of that bridge and
  Mathlib's `AddMonoidHom` structure, not a second case analysis.

What Mathlib lacks, and what this file adds, is the transport over arbitrary commutative rings,
where `W.Point` has no group law to speak of.

The definition needs only injectivity, since that is what `Affine.map_nonsingular` needs to carry
nonsingularity across. Negation and the functorial laws hold over any commutative ring and are
proved here at that generality.

This supports the Hasse strand of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 3: the Silverman
V.1 route counts `#E(𝔽_q)` as the fixed points of Frobenius, which means transporting points along
the `q`-power ring homomorphism and knowing that transport respects the group law and `ℤ`-multiples.
The roadmap's §"What Mathlib already has (consume)" lists `Affine.Point` and its `AddCommGroup` as
consumed infrastructure whose "infrastructure is load-bearing API here, not an implementation
detail"; this is a complement to that API, not a reimplementation of it.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/EC/AffinePointMap.lean`,
declarations `map`, `map_zero`, `map_some` and `map_neg`.

The source's `map_add`, `mapAddMonoidHom` and `map_zsmul` are deliberately **not** ported. Over a
field they are Mathlib's `Affine.Point.map` under `f.toAlgebra`, and `mapRingHom_eq_map` below is
the bridge to it; restating them here would duplicate Mathlib's own case analysis.

Changes from the source. The names take a `RingHom` suffix, Mathlib having since taken
`Point.map` for the `AlgHom` version. The computation rules are stated in simp-normal form, and
negation and the functorial laws are stated over an arbitrary commutative ring rather than a field.
The identity, composition and injectivity laws have no counterpart in the source.
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

/-- The point map sends the point at infinity to the point at infinity. -/
@[simp]
lemma mapRingHom_zero : mapRingHom f hf (0 : W.toAffine.Point) = 0 := by
  rfl

/-- The point map sends an affine point to the point with image coordinates. -/
@[simp]
lemma mapRingHom_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapRingHom f hf (.some x y h)
      = .some (f x) (f y) ((Affine.map_nonsingular W.toAffine hf x y).mpr h) := by
  simp [mapRingHom]

/-- **The point map preserves negation**, over any commutative ring. -/
@[simp]
lemma mapRingHom_neg (P : W.toAffine.Point) :
    mapRingHom f hf (-P) = -mapRingHom f hf P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some, mapRingHom_some, mapRingHom_some, Affine.Point.neg_some]
    simp only [Affine.map_negY]

/-- **The point map along the identity is the identity**, after Mathlib's `WeierstrassCurve.map_id`
identifies the codomain. -/
@[simp]
lemma mapRingHom_id (P : W.toAffine.Point) :
    mapRingHom (RingHom.id R) (fun _ _ h => h) P = _root_.WeierstrassCurve.map_id W ▸ P := by
  rcases P with _ | ⟨x, y, h⟩ <;> simp [mapRingHom]

/-- **The point map is functorial in the ring homomorphism**, after Mathlib's
`WeierstrassCurve.map_map` identifies the codomain. -/
lemma mapRingHom_mapRingHom {T : Type*} [CommRing T] (g : S →+* T) (hg : Function.Injective g)
    (P : W.toAffine.Point) :
    mapRingHom g hg (mapRingHom f hf P)
      = _root_.WeierstrassCurve.map_map W f g ▸ mapRingHom (g.comp f) (hg.comp hf) P := by
  rcases P with _ | ⟨x, y, h⟩ <;> simp [mapRingHom] <;> rfl

/-- **The point map is injective.** -/
lemma mapRingHom_injective : Function.Injective (mapRingHom f hf (W := W)) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hP <;> simp only [mapRingHom] at hP
  · rfl
  · exact absurd hP (by simp)
  · exact absurd hP (by simp)
  · obtain ⟨hx, hy⟩ := Affine.Point.some.inj hP
    simp only [hf hx, hf hy]


section Field

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  {W : _root_.WeierstrassCurve F} (f : F →+* K)

/-- **Over a field the transport is Mathlib's `Affine.Point.map`**, for *any* ring homomorphism —
in particular for a `q`-power Frobenius, which is not an ambient `algebraMap`. Giving `K` the
`F`-algebra structure `f` induces makes the two constructions the same map. -/
lemma mapRingHom_eq_map (P : W.toAffine.Point) :
    letI : Algebra F K := f.toAlgebra
    mapRingHom f f.injective P = Affine.Point.map (W' := W) (Algebra.ofId F K) P := by
  let : Algebra F K := f.toAlgebra
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

/-- **The transport is additive over a field**, inherited from Mathlib's `Affine.Point.map` rather
than reproved. -/
lemma mapRingHom_add (P Q : W.toAffine.Point) :
    mapRingHom f f.injective (P + Q)
      = mapRingHom f f.injective P + mapRingHom f f.injective Q := by
  let : Algebra F K := f.toAlgebra
  simp only [mapRingHom_eq_map]
  exact (Affine.Point.map (W' := W) (Algebra.ofId F K)).map_add P Q

/-- **The transport respects `ℤ`-multiples**, inherited from Mathlib's `Affine.Point.map`. -/
lemma mapRingHom_zsmul (n : ℤ) (P : W.toAffine.Point) :
    mapRingHom f f.injective (n • P) = n • mapRingHom f f.injective P := by
  let : Algebra F K := f.toAlgebra
  simp only [mapRingHom_eq_map]
  exact (Affine.Point.map (W' := W) (Algebra.ofId F K)).map_zsmul n P

end Field

end WeierstrassCurve.Affine.Point

end TauCeti

end
