/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The ideal of a point of a Weierstrass curve is maximal, and determines the point

For a point `(x, y)` on an affine Weierstrass curve `W` over a field, Mathlib's
`CoordinateRing.XYIdeal W x (C y)` is the ideal `⟨X - x, Y - y⟩` of the coordinate ring, and
`CoordinateRing.quotientXYIdealEquiv` identifies the quotient by it with the base field. This file
records the consequences: that ideal is maximal, it is nonzero, and it determines the point it
came from.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot`: `XYIdeal W x y` is nonzero, over
  any nontrivial commutative base.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal`: `XYIdeal W x y` is maximal
  for any `y : F[X]` solving the Weierstrass equation at `x`, matching the generality of
  `XYIdeal` and `quotientXYIdealEquiv` themselves.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation`: the point case,
  `XYIdeal W x (C y)` for `(x, y)` on `W`.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_inj`: distinct points give distinct
  ideals. Only properness of the ideal is used: both `X - x₁` and `X - x₂` lie in it, so the
  constant `x₂ - x₁` does too, and a nonzero constant would be a unit; likewise for `Y`.

Mathlib has the quotient isomorphism but records nothing about the ideal itself; the many `XYIdeal`
lemmas it does state (`XYIdeal_eq₁`, `XYIdeal_eq₂`, `XYIdeal_mul_XYIdeal`, `XYIdeal_neg_mul`) are
all about products and rewriting, not about the ideal's place in the spectrum. It does record that
the two generators are nonzero (`XClass_ne_zero`, `YClass_ne_zero`), which is what `XYIdeal_ne_bot`
rests on.

Only the curve equation is needed, not nonsingularity: the quotient is the base field either way.

This supports `TauCetiRoadmap/EllipticCurves/README.md`, Layer 0, whose point–place dictionary
identifies the affine places of `W` with the maximal ideals of its coordinate ring — "the affine
places are the maximal ideals of the coordinate ring". Maximality of `XYIdeal` is the direction
that sends a point to a place, and `XYIdeal_inj` is the direction that recovers the point, so the
two together make the correspondence injective. The roadmap's §"What Mathlib already has
(consume)" lists `Affine.CoordinateRing` as consumed infrastructure that "is load-bearing API
here, not an
implementation detail"; this is a complement to that API, not a reimplementation of it.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Curves/Basic.lean`, declaration
`maximalIdealAt_isMaximal`. `XYIdeal_inj` is not in the source.

Changes from the source. There the ideal is reached through a `SmoothPlaneCurve` structure wrapping
`WeierstrassCurve.Affine` and a `SmoothPoint` structure bundling the coordinates with their
nonsingularity proof; the surrounding wrappers are not ported, and the statement is made directly
about Mathlib's `XYIdeal`. The hypothesis is correspondingly weakened from nonsingularity to the
curve equation, which is all the quotient isomorphism consumes.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti

namespace WeierstrassCurve.Affine.CoordinateRing

section CommRing

variable {R : Type*} [CommRing R] [Nontrivial R] {W : _root_.WeierstrassCurve.Affine R}

/-- **The ideal `⟨X - x, Y - y(X)⟩` of the coordinate ring is nonzero** over a nontrivial base. -/
@[simp]
lemma XYIdeal_ne_bot (x : R) (y : R[X]) : CoordinateRing.XYIdeal W x y ≠ ⊥ := fun hbot => by
  have hmem : CoordinateRing.XClass W x ∈ CoordinateRing.XYIdeal W x y :=
    Ideal.subset_span (Set.mem_insert _ _)
  rw [hbot, Ideal.mem_bot] at hmem
  exact CoordinateRing.XClass_ne_zero x hmem

end CommRing

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} {x : F}

/-- **The ideal `⟨X - x, Y - y(X)⟩` of the coordinate ring is maximal** whenever `y` is a
polynomial solving the Weierstrass equation at `x`. Equivalently, the quotient by it is the base
field. -/
theorem XYIdeal_isMaximal {y : F[X]} (h : (W.polynomial.eval y).eval x = 0) :
    (CoordinateRing.XYIdeal W x y).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((CoordinateRing.quotientXYIdealEquiv h).toRingEquiv.isField (Field.toIsField F))

/-- **The ideal of a point of a Weierstrass curve is maximal**, the constant-polynomial case of
`XYIdeal_isMaximal`. -/
theorem XYIdeal_isMaximal_of_equation {y : F} (h : W.Equation x y) :
    (CoordinateRing.XYIdeal W x (C y)).IsMaximal :=
  XYIdeal_isMaximal h

/-- A proper ideal of the coordinate ring contains no nonzero constant: constants from the base
field are units. -/
private theorem eq_zero_of_algebraMap_mem {I : Ideal W.CoordinateRing} (hI : I ≠ ⊤) {c : F}
    (hc : algebraMap F W.CoordinateRing c ∈ I) : c = 0 := by
  by_contra hne
  exact hI (I.eq_top_of_isUnit_mem hc ((IsUnit.mk0 c hne).map (algebraMap F W.CoordinateRing)))

/-- The image of a base-field element in the coordinate ring is `mk` of the double constant. -/
private theorem algebraMap_eq_mk (c : F) :
    algebraMap F W.CoordinateRing c = CoordinateRing.mk W (C (C c)) :=
  rfl

/-- Two `XClass` generators differ by the constant `x₂ - x₁`. -/
private theorem XClass_sub_XClass (x₁ x₂ : F) :
    CoordinateRing.XClass W x₁ - CoordinateRing.XClass W x₂ =
      algebraMap F W.CoordinateRing (x₂ - x₁) := by
  simp only [CoordinateRing.XClass, algebraMap_eq_mk, ← map_sub]
  congr 1
  simp only [map_sub]
  ring

/-- Two `YClass` generators at constants differ by the constant `y₂ - y₁`. -/
private theorem YClass_sub_YClass (y₁ y₂ : F) :
    CoordinateRing.YClass W (C y₁) - CoordinateRing.YClass W (C y₂) =
      algebraMap F W.CoordinateRing (y₂ - y₁) := by
  simp only [CoordinateRing.YClass, algebraMap_eq_mk, ← map_sub]
  congr 1
  simp only [map_sub]
  ring

/-- **Distinct points of the curve have distinct ideals.** Together with `XYIdeal_isMaximal`, this
is the point–place dictionary in both directions: a point determines a maximal ideal, and the point
is recoverable from it.

The argument needs only that the ideal is proper. Both `X - x₁` and `X - x₂` lie in it, so their
difference — the constant `x₂ - x₁` — does too, and a nonzero constant would be a unit; the same
for the `Y` generators. -/
theorem XYIdeal_inj {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h : CoordinateRing.XYIdeal W x₁ (C y₁) = CoordinateRing.XYIdeal W x₂ (C y₂)) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hI : CoordinateRing.XYIdeal W x₁ (C y₁) ≠ ⊤ := (XYIdeal_isMaximal_of_equation h₁).ne_top
  have hmemX : CoordinateRing.XClass W x₁ - CoordinateRing.XClass W x₂ ∈
      CoordinateRing.XYIdeal W x₁ (C y₁) :=
    Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert _ _))
      (h ▸ Ideal.subset_span (Set.mem_insert _ _))
  have hmemY : CoordinateRing.YClass W (C y₁) - CoordinateRing.YClass W (C y₂) ∈
      CoordinateRing.XYIdeal W x₁ (C y₁) :=
    Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      (h ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [XClass_sub_XClass] at hmemX
  rw [YClass_sub_YClass] at hmemY
  exact ⟨(sub_eq_zero.mp (eq_zero_of_algebraMap_mem hI hmemX)).symm,
    (sub_eq_zero.mp (eq_zero_of_algebraMap_mem hI hmemY)).symm⟩

end WeierstrassCurve.Affine.CoordinateRing

end TauCeti

end
