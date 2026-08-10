/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The ideal of a point of a Weierstrass curve is maximal, and determines its coordinates

For a point `(x, y)` on an affine Weierstrass curve `W` over a field, Mathlib's
`CoordinateRing.XYIdeal W x (C y)` is the ideal `⟨X - x, Y - y⟩` of the coordinate ring, and
`CoordinateRing.quotientXYIdealEquiv` identifies the quotient by it with the base field. This file
records the consequences: that ideal is maximal, it is nonzero, and it determines the coordinates
it was built from.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot`: `XYIdeal W x y` is nonzero, over
  any nontrivial commutative base.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal`: `XYIdeal W x y` is maximal
  for any `y : F[X]` solving the Weierstrass equation at `x`, matching the generality of
  `XYIdeal` and `quotientXYIdealEquiv` themselves.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation`: the point case,
  `XYIdeal W x (C y)` for `(x, y)` on `W`.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff_of_ne_top`: two such ideals are
  equal exactly when their coordinates are, as soon as the first is proper. Forward: both
  `X - x₁` and `X - x₂` lie in the ideal, so the constant `x₂ - x₁` does too, and a nonzero
  constant would be a unit; likewise for `Y`.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff`: the point case, where properness
  comes from maximality.

Mathlib has the quotient isomorphism but records nothing about the ideal itself; the many `XYIdeal`
lemmas it does state (`XYIdeal_eq₁`, `XYIdeal_eq₂`, `XYIdeal_mul_XYIdeal`, `XYIdeal_neg_mul`) are
all about products and rewriting, not about the ideal's place in the spectrum. It does record that
the two generators are nonzero (`XClass_ne_zero`, `YClass_ne_zero`), which is what `XYIdeal_ne_bot`
rests on.

Only the curve equation is needed, not nonsingularity: the quotient is the base field either way.

This supports `TauCetiRoadmap/EllipticCurves/README.md`, Layer 0, whose point–place dictionary
identifies the affine places of `W` with the maximal ideals of its coordinate ring — "the affine
places are the maximal ideals of the coordinate ring". Maximality of `XYIdeal` is the direction
that sends a point to a place, and `XYIdeal_eq_iff` says that map is injective. Classifying *all*
maximal ideals as coming from points is a separate statement, not proved here.

The roadmap's §"What Mathlib already has (consume)" lists `Affine.CoordinateRing` as consumed
infrastructure that "is load-bearing API here, not an
implementation detail"; this is a complement to that API, not a reimplementation of it.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Curves/Basic.lean`, declaration
`maximalIdealAt_isMaximal`. The two `XYIdeal_eq_iff` lemmas are not in the source.

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

/-- The image of a base-field element in the coordinate ring is `mk` of the double constant. Proved
through `AdjoinRoot`'s own `algebraMap` API rather than by `rfl`, so it does not depend on how the
algebra instances happen to unfold. -/
private theorem algebraMap_eq_mk (c : F) :
    algebraMap F W.CoordinateRing c = CoordinateRing.mk W (C (C c)) := by
  rw [AdjoinRoot.algebraMap_eq' (S := F), RingHom.comp_apply, Polynomial.algebraMap_eq]
  -- all that is left is `CoordinateRing.mk W = AdjoinRoot.mk W.polynomial`, which is what
  -- `CoordinateRing.mk` is defined to be; no algebra instance is being unfolded here
  rfl

/-- Two `XClass` generators differ by the constant `x₂ - x₁`. -/
private theorem XClass_sub_XClass (x₁ x₂ : F) :
    CoordinateRing.XClass W x₁ - CoordinateRing.XClass W x₂ =
      algebraMap F W.CoordinateRing (x₂ - x₁) := by
  simp only [CoordinateRing.XClass, algebraMap_eq_mk, ← map_sub]
  congr 1
  simp only [map_sub]
  ring

/-- Two `YClass` generators differ by the image of the polynomial `y₂ - y₁`. -/
private theorem YClass_sub_YClass (y₁ y₂ : F[X]) :
    CoordinateRing.YClass W y₁ - CoordinateRing.YClass W y₂ =
      CoordinateRing.mk W (C (y₂ - y₁)) := by
  simp only [CoordinateRing.YClass, ← map_sub]
  congr 1
  simp only [map_sub]
  ring

/-- Modulo `X - x`, a polynomial in `X` is its value at `x`: the two differ by an explicit multiple
of the `XClass` generator. -/
private theorem mk_C_sub_algebraMap_eval (x : F) (y : F[X]) :
    ∃ q : F[X], CoordinateRing.mk W (C y) - algebraMap F W.CoordinateRing (y.eval x) =
      CoordinateRing.XClass W x * CoordinateRing.mk W (C q) := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := x) (p := y)
  refine ⟨q, ?_⟩
  rw [algebraMap_eq_mk, CoordinateRing.XClass, ← map_mul, ← map_sub, ← map_sub, ← C_mul, ← hq]

/-- **Two such ideals are equal exactly when their data agree at the point**, given only that the
first is proper: the `X`-coordinates must coincide, and the two `Y`-polynomials must take the same
value there. For the forward direction, both `X - x₁` and `X - x₂` lie in the ideal, so their
difference — the constant `x₂ - x₁` — does too, and a nonzero constant would be a unit; the `Y`
generators differ by `y₂ - y₁`, which reduces modulo `X - x₁` to its value at `x₁`. Stated for
polynomial `y`, matching `XYIdeal` and `XYIdeal_isMaximal`; no curve equation is needed. -/
theorem XYIdeal_eq_iff_of_ne_top {x₁ x₂ : F} {y₁ y₂ : F[X]}
    (hI : CoordinateRing.XYIdeal W x₁ y₁ ≠ ⊤) :
    CoordinateRing.XYIdeal W x₁ y₁ = CoordinateRing.XYIdeal W x₂ y₂ ↔
      x₁ = x₂ ∧ y₁.eval x₁ = y₂.eval x₂ := by
  have hX₁ : CoordinateRing.XClass W x₁ ∈ CoordinateRing.XYIdeal W x₁ y₁ :=
    Ideal.subset_span (Set.mem_insert _ _)
  constructor
  · intro h
    have hmemX : CoordinateRing.XClass W x₁ - CoordinateRing.XClass W x₂ ∈
        CoordinateRing.XYIdeal W x₁ y₁ :=
      Ideal.sub_mem _ hX₁ (h ▸ Ideal.subset_span (Set.mem_insert _ _))
    rw [XClass_sub_XClass] at hmemX
    have hx : x₁ = x₂ := (sub_eq_zero.mp (eq_zero_of_algebraMap_mem hI hmemX)).symm
    have hmemY : CoordinateRing.mk W (C (y₂ - y₁)) ∈ CoordinateRing.XYIdeal W x₁ y₁ := by
      rw [← YClass_sub_YClass]
      exact Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
        (h ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    obtain ⟨q, hq⟩ := mk_C_sub_algebraMap_eval (W := W) x₁ (y₂ - y₁)
    have : algebraMap F W.CoordinateRing ((y₂ - y₁).eval x₁) ∈
        CoordinateRing.XYIdeal W x₁ y₁ := by
      have := Ideal.sub_mem _ hmemY (hq ▸ Ideal.mul_mem_right (CoordinateRing.mk W (C q)) _ hX₁)
      simpa using this
    have := eq_zero_of_algebraMap_mem hI this
    rw [eval_sub, sub_eq_zero] at this
    exact ⟨hx, by rw [← hx, this]⟩
  · rintro ⟨rfl, hy⟩
    -- the two `Y` generators differ by a multiple of `X - x₁`, so the spans agree
    obtain ⟨q, hq⟩ := mk_C_sub_algebraMap_eval (W := W) x₁ (y₂ - y₁)
    rw [eval_sub, sub_eq_zero.mpr hy.symm, map_zero, sub_zero] at hq
    have hdiff : CoordinateRing.YClass W y₁ - CoordinateRing.YClass W y₂ ∈
        Ideal.span {CoordinateRing.XClass W x₁} := by
      rw [YClass_sub_YClass, hq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have hle : ∀ z₁ z₂ : F[X], CoordinateRing.YClass W z₁ - CoordinateRing.YClass W z₂ ∈
        Ideal.span {CoordinateRing.XClass W x₁} →
        CoordinateRing.XYIdeal W x₁ z₁ ≤ CoordinateRing.XYIdeal W x₁ z₂ := by
      intro z₁ z₂ hz
      rw [CoordinateRing.XYIdeal, Ideal.span_le]
      rintro w (rfl | rfl)
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · have hsub : Ideal.span {CoordinateRing.XClass W x₁} ≤ CoordinateRing.XYIdeal W x₁ z₂ := by
          rw [Ideal.span_le]
          rintro _ rfl
          exact Ideal.subset_span (Set.mem_insert _ _)
        have := Ideal.add_mem _ (hsub hz)
          (Ideal.subset_span (Set.mem_insert_of_mem _ rfl) :
            CoordinateRing.YClass W z₂ ∈ CoordinateRing.XYIdeal W x₁ z₂)
        simpa using this
    exact le_antisymm (hle y₁ y₂ hdiff) (hle y₂ y₁ (by simpa using neg_mem hdiff))

/-- **The ideal of a point determines the point**: for points of the curve, equality of the ideals
`⟨X - x, Y - y⟩` is equality of the coordinates, so `fun (x, y) ↦ XYIdeal W x (C y)` is injective
on points. The point case of `XYIdeal_eq_iff_of_ne_top`, whose properness comes from
`XYIdeal_isMaximal_of_equation`. -/
theorem XYIdeal_eq_iff {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) :
    CoordinateRing.XYIdeal W x₁ (C y₁) = CoordinateRing.XYIdeal W x₂ (C y₂) ↔
      x₁ = x₂ ∧ y₁ = y₂ := by
  simpa only [eval_C] using XYIdeal_eq_iff_of_ne_top (x₂ := x₂) (y₂ := C y₂)
    (XYIdeal_isMaximal_of_equation h₁).ne_top

end WeierstrassCurve.Affine.CoordinateRing

end TauCeti

end
