/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.NonUnitalHom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree

/-!
# The carrier of `Hom(W₁, W₂)`

An `Isogeny` is nonzero by construction: its pullback is injective, so there is no isogeny
representing the zero morphism. The zero morphism has no pullback of functions at all — it sends
every point to the target's point at infinity, which is not a point of the affine coordinate ring's
spectrum — so it cannot be added to the isogenies as another pullback.

This file carves the hom carrier out of a slightly larger mapping type instead, **adjoining
nothing**: the `F`-linear *multiplicative* maps `R(W₂) → K(W₁)`, which include the zero map because
multiplicativity does not force `1 ↦ 1`. Into a field there is nothing else new — `p 1` is
idempotent, so `NonUnitalAlgHom.eq_zero_or_map_one` splits the type as the zero map together with
the unital maps, and a unital map with the pointedness condition is exactly an `Isogeny`. So the
carrier is `{0} ⊔ Isogeny W₁ W₂` as a *set*, obtained by weakening unitality rather than by a
`WithZero` adjunction.

The zero element is a formal tag. No compatibility between it and composition of morphisms is
claimed: the pullback identity a nonzero morphism satisfies is vacuous at zero, every point
landing at infinity.

## Main definitions

* `TauCeti.Isogeny.IsHomPullback`: the condition carving the carrier out — a map that is unital
  is pointed.
* `TauCeti.Isogeny.Hom`: the carrier of `Hom(W₁, W₂)`, with `0` its zero map and
  `TauCeti.Isogeny.Hom.ofIsogeny` its nonzero elements.
* `TauCeti.Isogeny.Hom.degree`: the degree, extended by the stipulation `degree 0 = 0`.

## Main results

* `TauCeti.Isogeny.Hom.eq_zero_or_exists_ofIsogeny`: every element is the zero map or comes from
  a unique isogeny.
* `TauCeti.Isogeny.Hom.ofIsogeny_injective` and `TauCeti.Isogeny.Hom.ofIsogeny_ne_zero`: the
  isogenies sit in the carrier as distinct nonzero elements.

The additive structure is **not** here. A sum of multiplicative maps is not multiplicative, so
the carrier is not an additive subgroup of the linear maps; addition comes from the group law and
is a milestone of its own.
-/

public section

namespace TauCeti.Isogeny

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- The condition carving the hom carrier out of the non-unital pullbacks: if the map is unital,
it is pointed. At the zero map the hypothesis is unsatisfiable, so the condition is vacuous
there — which is what lets the zero map into the carrier without a pointedness claim about it. -/
-- `@[expose]` here and on the two constructions below: the members of this type are built and
-- taken apart by their underlying map, so consumers need that body, and the `rfl` lemmas
-- recording it are exported.
@[expose]
def IsHomPullback (p : W₂.CoordinateRing →ₙₐ[F] W₁.FunctionField) : Prop :=
  ∀ h : p 1 = 1, CoordinatePullback.MapsInfinity (p.toAlgHomOfMapOne h)

/-- **The carrier of `Hom(W₁, W₂)`**: an `F`-linear multiplicative map out of the target
coordinate ring, pointed wherever it is unital. Its zero map is the zero morphism's formal
representative and its unital elements are the isogenies. -/
@[ext]
structure Hom (W₁ W₂ : WeierstrassCurve.Affine F) where
  /-- The underlying multiplicative map. Not an `AlgHom`: unitality is what the zero map fails. -/
  toNonUnitalAlgHom : W₂.CoordinateRing →ₙₐ[F] W₁.FunctionField
  /-- Pointedness, required only of the unital maps. -/
  isHomPullback : IsHomPullback toNonUnitalAlgHom

namespace Hom

noncomputable instance : Zero (Hom W₁ W₂) where
  zero := ⟨0, fun h => absurd h (by simp)⟩

@[simp]
theorem toNonUnitalAlgHom_zero : (0 : Hom W₁ W₂).toNonUnitalAlgHom = 0 := rfl

/-- An isogeny, as an element of the carrier. -/
@[expose]
noncomputable def ofIsogeny (φ : Isogeny W₁ W₂) : Hom W₁ W₂ where
  toNonUnitalAlgHom := (φ.pullback : W₂.CoordinateRing →ₙₐ[F] W₁.FunctionField)
  isHomPullback _ := φ.mapsInfinity

-- Not `@[simp]`: it rewrites `ofIsogeny_apply`'s left-hand side, and `simpNF` rejects the pair.
-- The applied form keeps the attribute, being the one a consumer meets.
theorem toNonUnitalAlgHom_ofIsogeny (φ : Isogeny W₁ W₂) :
    (ofIsogeny φ).toNonUnitalAlgHom = (φ.pullback : W₂.CoordinateRing →ₙₐ[F] W₁.FunctionField) :=
  rfl

@[simp]
theorem ofIsogeny_apply (φ : Isogeny W₁ W₂) (x : W₂.CoordinateRing) :
    (ofIsogeny φ).toNonUnitalAlgHom x = φ.pullback x :=
  rfl

theorem ofIsogeny_injective : Function.Injective (ofIsogeny (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h => Isogeny.ext (AlgHom.ext fun x => congrArg (fun g => g.toNonUnitalAlgHom x) h)

@[simp]
theorem ofIsogeny_ne_zero (φ : Isogeny W₁ W₂) : ofIsogeny φ ≠ 0 := fun h => by
  refine one_ne_zero (α := W₁.FunctionField) ?_
  calc (1 : W₁.FunctionField)
      = φ.pullback 1 := (map_one _).symm
    _ = (ofIsogeny φ).toNonUnitalAlgHom 1 := rfl
    _ = (0 : Hom W₁ W₂).toNonUnitalAlgHom 1 := by rw [h]
    _ = 0 := rfl

/-- **Every element of the carrier is the zero map or an isogeny.** This is the dichotomy the
carrier is built for: weakening unitality admits the zero map and nothing else. -/
theorem eq_zero_or_exists_ofIsogeny (h : Hom W₁ W₂) :
    h = 0 ∨ ∃ φ : Isogeny W₁ W₂, h = ofIsogeny φ := by
  rcases h.toNonUnitalAlgHom.eq_zero_or_map_one with hz | hone
  · exact Or.inl (Hom.ext (hz.trans toNonUnitalAlgHom_zero.symm))
  · exact Or.inr ⟨⟨h.toNonUnitalAlgHom.toAlgHomOfMapOne hone, h.isHomPullback hone⟩, Hom.ext rfl⟩

/-- The isogeny an element comes from, when it is not the zero map. -/
noncomputable def toIsogeny {h : Hom W₁ W₂} (hz : h ≠ 0) : Isogeny W₁ W₂ :=
  ⟨h.toNonUnitalAlgHom.toAlgHomOfMapOne (NonUnitalAlgHom.map_one_of_ne_zero (fun hn =>
      hz (Hom.ext (hn.trans toNonUnitalAlgHom_zero.symm)))),
    h.isHomPullback _⟩

@[simp]
theorem ofIsogeny_toIsogeny {h : Hom W₁ W₂} (hz : h ≠ 0) : ofIsogeny (toIsogeny hz) = h :=
  Hom.ext rfl

/-- **The degree**, extended to the carrier by stipulating `degree 0 = 0`: the zero map's image
generates no field, so there is no extension for a dimension to measure. -/
noncomputable def degree (h : Hom W₁ W₂) : ℕ := by
  classical exact if hz : h = 0 then 0 else (toIsogeny hz).degree

@[simp]
theorem degree_zero : (0 : Hom W₁ W₂).degree = 0 := by
  classical simp [degree]

@[simp]
theorem degree_ofIsogeny (φ : Isogeny W₁ W₂) : (ofIsogeny φ).degree = φ.degree := by
  classical
  rw [degree]
  split
  · exact absurd ‹ofIsogeny φ = 0› (ofIsogeny_ne_zero φ)
  · rw [ofIsogeny_injective (ofIsogeny_toIsogeny _)]

end Hom

end TauCeti.Isogeny

end
