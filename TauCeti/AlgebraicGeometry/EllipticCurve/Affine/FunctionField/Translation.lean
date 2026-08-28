/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.FieldTheory.AlgebraicClosure
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint

/-!
# The translation action of the point group on the function field

For a point `P` of an elliptic curve `W` over a field `F`, the translation `τ_P : Q ↦ Q + P` is an
automorphism of the curve — of the curve, not of the elliptic curve: it does not fix the point at
infinity unless `P = O`, so it is not an isogeny. What it does induce is an `F`-algebra
automorphism `τ_P^*` of the function field `F(W)`, and `P ↦ τ_P^*` is a faithful action of the
point group on `F(W)`. This file constructs that action.

The construction runs through the generic point `g` of
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/GenericPoint.lean`. Translating a
function by `P` is evaluating it at `g + P`, so the pullback of `τ_P` on the affine coordinate ring
is `CoordinateRing.evalAlgHom` at the coordinates of the translate `g + P_{F(W)}`, and the
composition law is the associativity of the point group: applying `τ_Q^*` to a coordinate of
`g + P` moves the generic point to `g + Q`, hence the pair to `g + P + Q`.

Two facts make the construction go through, and both come down to the transcendence of the
coordinate function `x`. First, `g + P` is never the point at infinity, since otherwise `g` would
be a constant point. Second, its `x`-coordinate is again transcendental: were it algebraic, the
Weierstrass equation — monic of degree `2` in `y` — would make its `y`-coordinate algebraic too, so
`g + P` would be a point over the relative algebraic closure of `F` in `F(W)`, and subtracting the
constant point `P` would put `g` there as well. Transcendence is what makes the evaluation map
injective (`CoordinateRing.algHom_injective`) and so extendable to the fraction field.

## Main definitions

* `WeierstrassCurve.Affine.translatedPoint`: the translate `g + P` of the generic point.
* `WeierstrassCurve.Affine.translation`: the automorphism `τ_P^*` of the function field.
* `WeierstrassCurve.Affine.translationHom`: the action, as a monoid homomorphism out of
  `Multiplicative W.Point`.

## Main results

* `WeierstrassCurve.Affine.translation_zero` and
  `WeierstrassCurve.Affine.translation_add`: the action laws, `τ_O^* = 1` and
  `τ_{P + Q}^* = τ_P^* ≫ τ_Q^*`.
* `WeierstrassCurve.Affine.translation_eq_one_iff` and
  `WeierstrassCurve.Affine.translation_injective` and
  `WeierstrassCurve.Affine.translationHom_injective`: the action is faithful.
* `WeierstrassCurve.Affine.translation_apply_genericX_some` and
  `WeierstrassCurve.Affine.translation_apply_genericY_some`: for an affine `P` the two
  coordinate functions are moved by the Weierstrass addition formulas, which is what identifies
  this automorphism with the pullback of `τ_P`.

`[DecidableEq F]` is Mathlib's hypothesis for the group law on `Affine.Point`, and it is inherited
here; the function field gets its own instance from it, so the points of `W⁄F(W)` are available
with no further assumption.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0.5**, third milestone: "function-field
pullbacks of the translations `τ_P`, with the action and composition laws". Layer 1's dual-isogeny
milestone consumes them — "`Kˢᵉᵖ(W₁)/φ^*Kˢᵉᵖ(W₂)` **is** Galois with group `ker φ(Kˢᵉᵖ)` acting by
translations" — and so does the place-free fibre count of Layer 1, where "translation moves the
kernel fibre onto one".

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.4.

## Provenance

Not a port: none of the pinned sources builds the translation action. The pullback is manufactured
from Mathlib's `Affine.Point` group law rather than from the addition formulas directly, so the
composition law is the associativity Mathlib already proved.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : _root_.WeierstrassCurve.Affine F)
  [W.IsElliptic]

/-- The points of `W`, base changed to the function field of `W`. An abbreviation local to this
file: the public API is Mathlib's `Point.baseChange`. -/
private noncomputable def baseChangePoint : W.Point →+ (W⁄W.FunctionField).toAffine.Point :=
  Point.baseChange (W' := W) F W.FunctionField

omit [W.IsElliptic] in
/-- **Base change to the function field is injective on points.** -/
private theorem baseChangePoint_injective : Function.Injective (baseChangePoint W) :=
  Point.map_injective (W' := W) _

omit [W.IsElliptic] in
/-- The base change of an affine point is the affine point with the same coordinates. -/
private theorem baseChangePoint_some {x₁ y₁ : F} (h : W.Nonsingular x₁ y₁)
    (hh : (W⁄W.FunctionField).toAffine.Nonsingular (algebraMap F W.FunctionField x₁)
      (algebraMap F W.FunctionField y₁)) :
    baseChangePoint W (.some x₁ y₁ h) = .some _ _ hh :=
  Point.map_some (W' := W) (Algebra.ofId F W.FunctionField) h

/-- The translate of the generic point of `W` by a point `P`. -/
noncomputable def translatedPoint (P : W.Point) : (W⁄W.FunctionField).toAffine.Point :=
  genericPoint W + baseChangePoint W P

@[simp]
theorem translatedPoint_zero : translatedPoint W 0 = genericPoint W := by
  rw [translatedPoint, map_zero, add_zero]

omit [W.IsElliptic] in
private theorem xCoord_baseChangePoint (P : W.Point) :
    Point.xCoord (baseChangePoint W P) = algebraMap F W.FunctionField (Point.xCoord P) :=
  Point.map_xCoord (W := W) _ P

/-- **A translate of the generic point is never the point at infinity**: the coordinate `x` is
transcendental, so the generic point is not the negative of a constant point. -/
theorem translatedPoint_ne_zero (P : W.Point) : translatedPoint W P ≠ 0 := by
  intro h
  have hneg : genericPoint W = -baseChangePoint W P := by
    rw [eq_neg_iff_add_eq_zero]
    exact h
  have hx : genericX W = algebraMap F W.FunctionField (Point.xCoord P) := by
    rw [← xCoord_genericPoint, hneg, Point.xCoord_neg, xCoord_baseChangePoint]
  exact transcendental_genericX W (hx ▸ isAlgebraic_algebraMap _)

/-- **The `x`-coordinate of a translate of the generic point is transcendental.** Were it
algebraic, so would be the `y`-coordinate — the Weierstrass equation is monic of degree `2` in
`y` — so the translate would come from the relative algebraic closure of `F` in the function
field; subtracting the constant point `P` would put the generic point there too, making the
coordinate function `x` algebraic. -/
private theorem transcendental_xCoord_translatedPoint (P : W.Point) :
    Transcendental F (Point.xCoord (translatedPoint W P)) := by
  set 𝔽 := algebraicClosure F W.FunctionField with h𝔽
  intro halg
  set Q := translatedPoint W P with hQdef
  have hQ : Q ≠ 0 := translatedPoint_ne_zero W P
  set u := Point.xCoord Q with hu_def
  set v := Point.yCoord Q with hv_def
  have hns : (W⁄W.FunctionField).toAffine.Nonsingular u v := Point.nonsingular_coords hQ
  have hu : u ∈ 𝔽 := halg.isIntegral
  -- the second coordinate is a root of a monic quadratic over the algebraic closure
  have hb : (W⁄W.FunctionField).a₁ * u + (W⁄W.FunctionField).a₃ ∈ 𝔽 :=
    𝔽.add_mem (𝔽.mul_mem (𝔽.algebraMap_mem _) hu) (𝔽.algebraMap_mem _)
  have hc : -(u ^ 3 + (W⁄W.FunctionField).a₂ * u ^ 2 + (W⁄W.FunctionField).a₄ * u
      + (W⁄W.FunctionField).a₆) ∈ 𝔽 :=
    𝔽.neg_mem (𝔽.add_mem (𝔽.add_mem (𝔽.add_mem (𝔽.pow_mem hu 3)
      (𝔽.mul_mem (𝔽.algebraMap_mem _) (𝔽.pow_mem hu 2)))
      (𝔽.mul_mem (𝔽.algebraMap_mem _) hu)) (𝔽.algebraMap_mem _))
  have hv𝔽 : IsIntegral 𝔽 v := by
    refine ⟨X ^ 2 + (C (⟨_, hb⟩ : 𝔽) * X + C ⟨_, hc⟩), Polynomial.monic_X_pow_add ?_, ?_⟩
    · compute_degree
      norm_num
    · have heq := (_root_.WeierstrassCurve.Affine.equation_iff u v).1 hns.left
      have hb' : algebraMap 𝔽 W.FunctionField (⟨_, hb⟩ : 𝔽)
          = (W⁄W.FunctionField).a₁ * u + (W⁄W.FunctionField).a₃ := by
        simp only [IntermediateField.algebraMap_apply]
      have hc' : algebraMap 𝔽 W.FunctionField (⟨_, hc⟩ : 𝔽)
          = -(u ^ 3 + (W⁄W.FunctionField).a₂ * u ^ 2 + (W⁄W.FunctionField).a₄ * u
            + (W⁄W.FunctionField).a₆) := by
        simp only [IntermediateField.algebraMap_apply]
      simp only [eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_X_pow, hb', hc']
      linear_combination heq
  have hv : v ∈ 𝔽 := isIntegral_trans (R := F) v hv𝔽
  -- the point therefore descends to the algebraic closure, and so does the generic point
  have hnsE : (W⁄𝔽).toAffine.Nonsingular (⟨u, hu⟩ : 𝔽) ⟨v, hv⟩ :=
    (_root_.WeierstrassCurve.Affine.baseChange_nonsingular (W := W)
      (f := 𝔽.val) 𝔽.val.injective _ _).1 hns
  have hQmap : Point.map 𝔽.val (Point.some (⟨u, hu⟩ : 𝔽) ⟨v, hv⟩ hnsE) = Q := by
    rw [Point.map_some]
    exact Point.some_coords hQ
  have hgeneric : genericPoint W =
      Point.map 𝔽.val (Point.some (⟨u, hu⟩ : 𝔽) ⟨v, hv⟩ hnsE -
        Point.baseChange (W' := W) F 𝔽 P) := by
    have hbc : Point.map 𝔽.val (Point.baseChange (W' := W) F 𝔽 P) = baseChangePoint W P :=
      Point.map_baseChange (W' := W) 𝔽.val P
    rw [map_sub, hQmap, hbc, hQdef, translatedPoint]
    exact (add_sub_cancel_right _ _).symm
  have : IsIntegral F (genericX W) := by
    rw [← xCoord_genericPoint, hgeneric, Point.map_xCoord]
    exact (Algebra.IsIntegral.isIntegral (R := F) _).map 𝔽.val
  exact transcendental_genericX W this.isAlgebraic

/-- The pullback of the translation by `P` on the affine coordinate ring: evaluation at the
translate of the generic point. -/
private noncomputable def translationAlgHom (P : W.Point) :
    W.CoordinateRing →ₐ[F] W.FunctionField :=
  CoordinateRing.evalAlgHom (Point.nonsingular_coords (translatedPoint_ne_zero W P)).left

private theorem translationAlgHom_mk_C_X (P : W.Point) :
    translationAlgHom W P (CoordinateRing.mk W (C X)) = Point.xCoord (translatedPoint W P) :=
  CoordinateRing.evalAlgHom_mk_C_X _

private theorem translationAlgHom_mk_Y (P : W.Point) :
    translationAlgHom W P (CoordinateRing.mk W Y) = Point.yCoord (translatedPoint W P) :=
  CoordinateRing.evalAlgHom_mk_Y _

private theorem translationAlgHom_injective (P : W.Point) :
    Function.Injective (translationAlgHom W P) :=
  CoordinateRing.algHom_injective _ <| by
    rw [translationAlgHom_mk_C_X]
    exact transcendental_xCoord_translatedPoint W P

/-- The pullback of the translation by `P` on the function field. -/
private noncomputable def translationAux (P : W.Point) :
    W.FunctionField →ₐ[F] W.FunctionField :=
  IsFractionRing.liftAlgHom (translationAlgHom_injective W P)

private theorem translationAux_algebraMap (P : W.Point) (z : W.CoordinateRing) :
    translationAux W P (algebraMap W.CoordinateRing W.FunctionField z) =
      translationAlgHom W P z := by
  simp [translationAux, IsFractionRing.liftAlgHom_apply]

private theorem translationAux_genericX (P : W.Point) :
    translationAux W P (genericX W) = Point.xCoord (translatedPoint W P) := by
  rw [genericX_def, translationAux_algebraMap, translationAlgHom_mk_C_X]

private theorem translationAux_genericY (P : W.Point) :
    translationAux W P (genericY W) = Point.yCoord (translatedPoint W P) := by
  rw [genericY_def, translationAux_algebraMap, translationAlgHom_mk_Y]

/-- **The translation pullback moves the generic point to its translate.** -/
private theorem map_genericPoint (P : W.Point) :
    Point.map (translationAux W P) (genericPoint W) = translatedPoint W P := by
  rw [genericPoint_eq_some, Point.map_some]
  refine Eq.trans ?_ (Point.some_coords (translatedPoint_ne_zero W P))
  congr 1
  · exact translationAux_genericX W P
  · exact translationAux_genericY W P

/-- **The translation pullback by `Q` carries the translate by `P` to the translate by `P + Q`.**
This is the group law of the points, transported to the function field. -/
private theorem map_translatedPoint (P Q : W.Point) :
    Point.map (translationAux W Q) (translatedPoint W P) = translatedPoint W (P + Q) := by
  have hbase : Point.map (translationAux W Q) (baseChangePoint W P) = baseChangePoint W P :=
    Point.map_baseChange (W' := W) (translationAux W Q) P
  rw [translatedPoint, map_add, hbase, map_genericPoint, translatedPoint, translatedPoint,
    map_add, add_right_comm]
  exact add_assoc _ _ _

/-- **Composition of translation pullbacks**, on the coordinate ring. -/
private theorem comp_translationAlgHom (P Q : W.Point) :
    (translationAux W Q).comp (translationAlgHom W P) = translationAlgHom W (P + Q) := by
  refine CoordinateRing.algHom_ext ?_ ?_
  · rw [AlgHom.comp_apply, translationAlgHom_mk_C_X, translationAlgHom_mk_C_X,
      ← Point.map_xCoord (W := W) (translationAux W Q), map_translatedPoint]
  · rw [AlgHom.comp_apply, translationAlgHom_mk_Y, translationAlgHom_mk_Y,
      ← Point.map_yCoord (W := W) (translationAux W Q), map_translatedPoint]

/-- **Composition of translation pullbacks**, on the function field. -/
private theorem comp_translationAux (P Q : W.Point) :
    (translationAux W Q).comp (translationAux W P) = translationAux W (P + Q) :=
  AlgHom.coe_ringHom_injective <| IsFractionRing.ringHom_ext (A := W.CoordinateRing) fun z ↦ by
    have h : translationAux W Q
        (translationAux W P (algebraMap W.CoordinateRing W.FunctionField z)) =
        translationAlgHom W (P + Q) z := by
      rw [translationAux_algebraMap, ← AlgHom.comp_apply, comp_translationAlgHom]
    simpa [translationAux_algebraMap] using h

/-- The translation by the point at infinity is the identity, on the coordinate ring. -/
private theorem translationAlgHom_zero :
    translationAlgHom W 0 = IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField := by
  refine CoordinateRing.algHom_ext ?_ ?_
  · rw [translationAlgHom_mk_C_X, translatedPoint_zero, xCoord_genericPoint,
      IsScalarTower.toAlgHom_apply, genericX_def]
  · rw [translationAlgHom_mk_Y, translatedPoint_zero, yCoord_genericPoint,
      IsScalarTower.toAlgHom_apply, genericY_def]

private theorem translationAux_zero : translationAux W 0 = AlgHom.id F W.FunctionField :=
  AlgHom.coe_ringHom_injective <| IsFractionRing.ringHom_ext (A := W.CoordinateRing) fun z ↦ by
    have h : translationAux W 0 (algebraMap W.CoordinateRing W.FunctionField z) =
        algebraMap W.CoordinateRing W.FunctionField z := by
      rw [translationAux_algebraMap, translationAlgHom_zero, IsScalarTower.toAlgHom_apply]
    simpa using h

/-- **The translation of the function field by a point `P`.** It is the pullback of the
translation `τ_P : Q ↦ Q + P` of the curve: on the affine coordinate ring it is evaluation at the
translate of the generic point by `P`, and its inverse is the translation by `-P`. -/
noncomputable def translation (P : W.Point) : W.FunctionField ≃ₐ[F] W.FunctionField :=
  AlgEquiv.ofAlgHom (translationAux W P) (translationAux W (-P))
    (by rw [comp_translationAux, neg_add_cancel, translationAux_zero])
    (by rw [comp_translationAux, add_neg_cancel, translationAux_zero])

/-- **The translation by the point at infinity is the identity.** -/
@[simp]
theorem translation_zero : translation W 0 = 1 :=
  AlgEquiv.ext fun z ↦ AlgHom.congr_fun (translationAux_zero W) z

/-- **The composition law of the translations.** Translating by `P` and then by `Q` is
translating by `P + Q`; on function fields the pullbacks compose in that same order, the point
group being commutative. -/
theorem translation_add (P Q : W.Point) :
    translation W (P + Q) = (translation W P).trans (translation W Q) :=
  AlgEquiv.ext fun z ↦ (AlgHom.congr_fun (comp_translationAux W P Q) z).symm

/-- **The translation action of the point group on the function field.** -/
noncomputable def translationHom :
    Multiplicative W.Point →* (W.FunctionField ≃ₐ[F] W.FunctionField) where
  toFun P := translation W (Multiplicative.toAdd P)
  map_one' := translation_zero W
  map_mul' P Q := by
    exact (congrArg (translation W)
      (add_comm (Multiplicative.toAdd P) (Multiplicative.toAdd Q))).trans
      (translation_add W (Multiplicative.toAdd Q) (Multiplicative.toAdd P))

@[simp]
theorem translationHom_apply (P : Multiplicative W.Point) :
    translationHom W P = translation W (Multiplicative.toAdd P) := (rfl)

/-- **The translation moves the coordinate `x` to the `x`-coordinate of the translate of the
generic point**: this is what makes `translation` the pullback of `τ_P`. -/
theorem translation_apply_genericX (P : W.Point) :
    translation W P (genericX W) = Point.xCoord (translatedPoint W P) :=
  translationAux_genericX W P

/-- **The translation moves the coordinate `y` to the `y`-coordinate of the translate of the
generic point.** -/
theorem translation_apply_genericY (P : W.Point) :
    translation W P (genericY W) = Point.yCoord (translatedPoint W P) :=
  translationAux_genericY W P

/-- **The translation action is faithful**: only the point at infinity acts trivially. Both
coordinates of the translate of the generic point being unmoved makes the translate the generic
point itself. -/
@[simp]
theorem translation_eq_one_iff {P : W.Point} : translation W P = 1 ↔ P = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ translation_zero W⟩
  have hx : Point.xCoord (translatedPoint W P) = Point.xCoord (genericPoint W) := by
    rw [← translation_apply_genericX, h, AlgEquiv.one_apply, xCoord_genericPoint]
  have hy : Point.yCoord (translatedPoint W P) = Point.yCoord (genericPoint W) := by
    rw [← translation_apply_genericY, h, AlgEquiv.one_apply, yCoord_genericPoint]
  have hpt : translatedPoint W P = genericPoint W := by
    rw [← Point.some_coords (translatedPoint_ne_zero W P), genericPoint_eq_some]
    congr 1
    · exact hx.trans (xCoord_genericPoint W)
    · exact hy.trans (yCoord_genericPoint W)
  rw [translatedPoint, add_eq_left] at hpt
  exact baseChangePoint_injective W (hpt.trans (map_zero (baseChangePoint W)).symm)

/-- **Distinct points induce distinct translations of the function field**: the action of the
point group is faithful, `translation W P = translation W Q` forcing `P = Q`. -/
theorem translation_injective : Function.Injective (translation W) := fun P Q h ↦ by
  have hPQ : translation W (P - Q) = 1 := by
    rw [sub_eq_add_neg, translation_add, h, ← translation_add, add_neg_cancel, translation_zero]
  rwa [translation_eq_one_iff, sub_eq_zero] at hPQ

/-- **The translation action homomorphism is injective**: the packaged action is faithful. -/
theorem translationHom_injective : Function.Injective (translationHom W) := fun P Q h ↦ by
  apply Multiplicative.toAdd.injective
  apply translation_injective W
  simpa only [translationHom_apply] using h

omit [DecidableEq F] [W.IsElliptic] in
/-- The generic point and a base-changed affine point are never in the degenerate case of the
addition formulas: their `x`-coordinates already differ. -/
private theorem not_genericX_eq_and_genericY_eq_negY (x₁ y₁ : F) :
    ¬(genericX W = algebraMap F W.FunctionField x₁ ∧
      genericY W = (W⁄W.FunctionField).toAffine.negY (algebraMap F W.FunctionField x₁)
        (algebraMap F W.FunctionField y₁)) := fun hc ↦ genericX_ne_algebraMap W x₁ hc.1

omit [DecidableEq F] [W.IsElliptic] in
/-- The base change of an affine point of `W` is nonsingular over the function field. -/
private theorem nonsingular_algebraMap {x₁ y₁ : F} (h : W.Nonsingular x₁ y₁) :
    (W⁄W.FunctionField).toAffine.Nonsingular (algebraMap F W.FunctionField x₁)
      (algebraMap F W.FunctionField y₁) :=
  (_root_.WeierstrassCurve.Affine.baseChange_nonsingular (W := W)
    (f := Algebra.ofId F W.FunctionField) (Algebra.ofId F W.FunctionField).injective x₁ y₁).2 h

/-- **The translation of the coordinate `x` by an affine point**, read off the addition
formulas: the generic point and a constant point are never in the degenerate case, the coordinate
`x` taking no constant value. -/
theorem translation_apply_genericX_some {x₁ y₁ : F} (h : W.Nonsingular x₁ y₁) :
    translation W (.some x₁ y₁ h) (genericX W) =
      (W⁄W.FunctionField).toAffine.addX (genericX W) (algebraMap F W.FunctionField x₁)
        ((W⁄W.FunctionField).toAffine.slope (genericX W) (algebraMap F W.FunctionField x₁)
          (genericY W) (algebraMap F W.FunctionField y₁)) := by
  rw [translation_apply_genericX, translatedPoint,
    baseChangePoint_some W h (nonsingular_algebraMap W h), genericPoint_eq_some,
    _root_.WeierstrassCurve.Affine.Point.add_some (not_genericX_eq_and_genericY_eq_negY W x₁ y₁),
    Point.xCoord_some]

/-- **The translation of the coordinate `y` by an affine point**, read off the addition
formulas. -/
theorem translation_apply_genericY_some {x₁ y₁ : F} (h : W.Nonsingular x₁ y₁) :
    translation W (.some x₁ y₁ h) (genericY W) =
      (W⁄W.FunctionField).toAffine.addY (genericX W) (algebraMap F W.FunctionField x₁)
        (genericY W)
        ((W⁄W.FunctionField).toAffine.slope (genericX W) (algebraMap F W.FunctionField x₁)
          (genericY W) (algebraMap F W.FunctionField y₁)) := by
  rw [translation_apply_genericY, translatedPoint,
    baseChangePoint_some W h (nonsingular_algebraMap W h), genericPoint_eq_some,
    _root_.WeierstrassCurve.Affine.Point.add_some (not_genericX_eq_and_genericY_eq_negY W x₁ y₁),
    Point.yCoord_some]

end WeierstrassCurve.Affine

end
