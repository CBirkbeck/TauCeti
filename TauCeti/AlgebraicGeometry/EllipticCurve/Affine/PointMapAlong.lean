/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The point map induced by a ring homomorphism

Mathlib's `WeierstrassCurve.Affine.Point.map` moves the points of a *fixed* curve between two
**field** extensions of a base, along an `AlgHom` in a scalar tower — which covers the `q`-power
Frobenius, Mathlib bundling that as `FiniteField.frobeniusAlgHom`. This file supplies the other
functoriality: an injective ring homomorphism `f : R →+* S` carries the points of `W` over `R` to
the points of the curve `W.map f` over `S`, with no fields and no tower involved.

## Main definitions and results

* `TauCeti.WeierstrassCurve.Affine.Point.mapAlong`: the map `W.Point → (W.map f).Point`, over
  arbitrary commutative rings.
* `TauCeti.WeierstrassCurve.Affine.Point.mapAlong_neg`, `mapAlong_id`,
  `mapAlong_mapAlong` and `mapAlong_injective`: the functorial API, over arbitrary
  commutative rings, mirroring Mathlib's
  `Affine.Point.map_id`, `map_map` and `map_injective` for the `AlgHom` version. The identity and
  composition laws transport their codomains along Mathlib's `WeierstrassCurve.map_id` and
  `map_map`.

* `TauCeti.WeierstrassCurve.Affine.Point.mapAlong_eq_map`: over a field, for **any** ring
  homomorphism `f`, the transport *is* Mathlib's `Affine.Point.map` once `K` carries the
  `F`-algebra structure `f` induces.
Over a field, `mapAlong_eq_map` is the whole story: the transport *is* Mathlib's
`Affine.Point.map`, which is already an `AddMonoidHom`. Rewriting with it gives `map_add`,
`map_zero` and `map_zsmul` from Mathlib directly. Nothing field-level is defined or restated
here — a bundled hom or `add`/`zsmul` lemmas would be a wrapper around Mathlib's.

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

The source's `map_add`, `mapAddMonoidHom` and `map_zsmul` are **not** ported. Over a field all
three are Mathlib's `Affine.Point.map` under `f.toAlgebra`, and `mapAlong_eq_map` is the bridge
to it; anything more here would be a wrapper.

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
noncomputable def mapAlong : W.toAffine.Point → (W.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((Affine.map_nonsingular W.toAffine hf x y).mpr h)

/-- The point map sends the point at infinity to the point at infinity. -/
@[simp]
lemma mapAlong_zero : mapAlong f hf (0 : W.toAffine.Point) = 0 := by
  rfl

/-- The point map sends an affine point to the point with image coordinates. -/
@[simp]
lemma mapAlong_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapAlong f hf (.some x y h)
      = .some (f x) (f y) ((Affine.map_nonsingular W.toAffine hf x y).mpr h) := by
  simp [mapAlong]

/-- **The point map preserves negation**, over any commutative ring. -/
@[simp]
lemma mapAlong_neg (P : W.toAffine.Point) :
    mapAlong f hf (-P) = -mapAlong f hf P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some, mapAlong_some, mapAlong_some, Affine.Point.neg_some]
    simp only [Affine.map_negY]

/-- **The point map along the identity is the identity.** `W.map (RingHom.id R)` is `W` by
definition, so no transport is needed. -/
@[simp]
lemma mapAlong_id (P : W.toAffine.Point) :
    mapAlong (RingHom.id R) (fun _ _ h => h) P = P := by
  rcases P with _ | ⟨x, y, h⟩ <;> simp [mapAlong]

/-- **The point map is functorial in the ring homomorphism.** `(W.map f).map g` is
`W.map (g.comp f)` by definition, so no transport is needed. -/
@[simp]
lemma mapAlong_mapAlong {T : Type*} [CommRing T] (g : S →+* T) (hg : Function.Injective g)
    (P : W.toAffine.Point) :
    mapAlong g hg (mapAlong f hf P) = mapAlong (g.comp f) (hg.comp hf) P := by
  rcases P with _ | ⟨x, y, h⟩ <;> simp [mapAlong] <;> rfl

/-- **The point map is injective.** -/
lemma mapAlong_injective : Function.Injective (mapAlong f hf (W := W)) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hP <;> simp only [mapAlong] at hP
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
lemma mapAlong_eq_map (P : W.toAffine.Point) :
    letI : Algebra F K := f.toAlgebra
    mapAlong f f.injective P = Affine.Point.map (W' := W) (Algebra.ofId F K) P := by
  let : Algebra F K := f.toAlgebra
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

end Field

end WeierstrassCurve.Affine.Point

end TauCeti

end
