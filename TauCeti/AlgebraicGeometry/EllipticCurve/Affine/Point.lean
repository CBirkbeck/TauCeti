/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Isomorphism of point groups induced by a change of variables

Mathlib's affine `Point` API provides the group homomorphism `WeierstrassCurve.Affine.Point.map`
induced by a change of the base field (for a *fixed* Weierstrass curve), but not the isomorphism
of point groups induced by an admissible change of variables between two *different*
curves. This file supplies that: for `C : VariableChange F` and a Weierstrass curve `W` over a
field `F` — no ellipticity hypothesis, matching Mathlib's point group — the admissible change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)` gives a group isomorphism
`(C • W).Point ≃+ W.Point`. All definitions are computable (given decidable equality on `F`):
the inverse of the isomorphism is given explicitly by the change of variables `C⁻¹`, not
obtained from bijectivity via choice.

The coordinate transformation laws (`negY`, `addX`, `addY`, `Equation`, `Nonsingular`) are
stated over an arbitrary commutative ring, matching the generality of Mathlib's
`WeierstrassCurve.Affine.Formula`; only the slope and the point group itself require a field.

## Main definitions

* `WeierstrassCurve.Affine.Point.mapVariableChange`: the group homomorphism
  `(C • W).Point →+ W.Point`, `(x, y) ↦ (u²x + r, u³y + u²sx + t)`.
* `WeierstrassCurve.Affine.Point.equivVariableChange`: the group isomorphism
  `(C • W).Point ≃+ W.Point`, with inverse coming from `C⁻¹` (transported along
  `inv_smul_smul` by Mathlib's `AddEquiv.cast`).

This is the variable-change point isomorphism that the quadratic-twist layer of
`TauCetiRoadmap/EllipticCurves/README.md` (§Layer 5) consumes: the twist point isomorphism
`quadraticTwistPointEquiv` there is assembled from this equivalence and Galois descent.

Adapted from the FLT project's quadratic-twist development (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, FLT PR #1088, merged there as
`bc2fe8ff7396`, Apache 2.0, by Michael Stoll and Claude). Following the repository's convention
for adapted material, the source authorship is credited here rather than in the copyright
header. Ported with the transformation laws generalised from a field to a commutative ring and
the ellipticity hypothesis removed.
-/

public section

namespace WeierstrassCurve.Affine

/-! ### Transformation of the group-law formulae under a change of variables

Throughout, the change of variables carries a point `(x, y)` of `C • W` to the point
`(u²x + r, u³y + u²sx + t)` of `W`. The laws in this section are stated over an arbitrary
commutative ring; `↑C.u⁻¹ * ↑C.u = 1` is fed to `grobner` to cancel the unit. -/

section Ring

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The change of variables intertwines negation: `negY` of the image point is the image of
`negY` of the original point. -/
lemma variableChange_negY (x y : R) :
    W.toAffine.negY ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 3 * (C • W).toAffine.negY x y + (C.u : R) ^ 2 * C.s * x + C.t := by
  have hu := C.u.inv_mul
  simp only [negY, variableChange_a₁, variableChange_a₃]
  grobner

/-- The change of variables intertwines the `x`-coordinate of addition: `addX` of the image
points along the transformed slope is the image of `addX` of the original points. -/
lemma variableChange_addX (x₁ x₂ ℓ : R) :
    W.toAffine.addX ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r) ((C.u : R) * ℓ + C.s)
      = (C.u : R) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  have hu := C.u.inv_mul
  simp only [addX, variableChange_a₁, variableChange_a₂]
  grobner

/-- The change of variables intertwines the negated `y`-coordinate of addition (`negAddY`). -/
lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : R) :
    W.toAffine.negAddY ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r)
        ((C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t) ((C.u : R) * ℓ + C.s)
      = (C.u : R) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : R) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [negAddY]
  rw [variableChange_addX]
  ring1

/-- The change of variables intertwines the `y`-coordinate of addition (`addY`). -/
lemma variableChange_addY (x₁ x₂ y₁ ℓ : R) :
    W.toAffine.addY ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r)
        ((C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t) ((C.u : R) * ℓ + C.s)
      = (C.u : R) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : R) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`: the
change of variables scales the Weierstrass polynomial by `u⁶`. -/
lemma variableChange_equation_iff (x y : R) :
    W.toAffine.Equation ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  have hu := C.u.inv_mul
  have key : W.toAffine.polynomial.evalEval ((C.u : R) ^ 2 * x + C.r)
      ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 6 * (C • W).toAffine.polynomial.evalEval x y := by
    simp only [evalEval_polynomial, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆]
    grobner
  unfold Equation
  rw [key]
  exact (C.u.isUnit.pow 6).mul_right_eq_zero

/-- The partial derivative `∂/∂y` of the Weierstrass polynomial at the image point is `u³` times
that of `C • W` at the original point. -/
lemma variableChange_evalEval_polynomialY (x y : R) :
    W.toAffine.polynomialY.evalEval ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y := by
  have hu := C.u.inv_mul
  simp only [evalEval_polynomialY, variableChange_a₁, variableChange_a₃]
  grobner

/-- The partial derivative `∂/∂x` of the Weierstrass polynomial at the image point, in terms of
the two partial derivatives of `C • W` at the original point (the chain rule for the change of
variables). -/
lemma variableChange_evalEval_polynomialX (x y : R) :
    W.toAffine.polynomialX.evalEval ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 4 * (C • W).toAffine.polynomialX.evalEval x y
        - C.s * ((C.u : R) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y) := by
  have hu := C.u.inv_mul
  simp only [evalEval_polynomialX, evalEval_polynomialY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄]
  grobner

/-- A point `(x, y)` is a nonsingular point of `C • W` if and only if its image
`(u²x + r, u³y + u²sx + t)` is a nonsingular point of `W`. This holds for an arbitrary
Weierstrass curve over a commutative ring — no ellipticity hypothesis. -/
lemma variableChange_nonsingular_iff (x y : R) :
    W.toAffine.Nonsingular ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Nonsingular x y := by
  have hX := variableChange_evalEval_polynomialX W C x y
  have hY := variableChange_evalEval_polynomialY W C x y
  unfold Nonsingular
  rw [variableChange_equation_iff, hX, hY]
  refine and_congr_right fun _ ↦ ?_
  rcases eq_or_ne ((C • W).toAffine.polynomialY.evalEval x y) 0 with hy | hy
  · simp only [hy, mul_zero, sub_zero, ne_eq, (C.u.isUnit.pow 4).mul_right_eq_zero]
  · exact iff_of_true (.inr fun h ↦ hy ((C.u.isUnit.pow 3).mul_right_eq_zero.mp h)) (.inr hy)

end Ring

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition (`negY`) only if the original pair does. -/
private lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
      (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro ⟨hX, hY⟩
  have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
  subst hx
  rw [variableChange_negY] at hY
  exact hxy ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY)⟩

/-- The change of variables transforms the slope of the line through two points affinely:
the slope through the image points is `u · ℓ + s` for `ℓ` the original slope. -/
lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hΦy : (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
        ≠ W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [variableChange_negY]
      exact fun h ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
    -- The tangent slope is `-∂x/∂y`, and the change of variables scales the two partial
    -- derivatives by `u⁴` (up to a multiple of `∂y`) and `u³`.
    have hPY : (C • W).toAffine.polynomialY.evalEval x₁ y₁ ≠ 0 := by
      rw [evalEval_polynomialY]
      exact fun h ↦ hy (by rw [negY]; linear_combination h)
    rw [W.toAffine.slope_of_Y_ne_eq_evalEval rfl hΦy,
      (C • W).toAffine.slope_of_Y_ne_eq_evalEval rfl hy,
      variableChange_evalEval_polynomialX, variableChange_evalEval_polynomialY]
    field
  · have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
    rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hΦx
    have h2 := sub_ne_zero.mpr hx
    field

/-! ### The induced isomorphism of point groups -/

namespace Point

variable [DecidableEq F]

/-- `AddEquiv.cast` between point groups sends an affine point to the affine point with the
same coordinates. Not a `simp` lemma: `simp` rewrites `AddEquiv.cast h` to a plain `cast`
first, so this left-hand side is not in normal form and would never fire. -/
lemma cast_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point) h (some x y hns)
      = some x y (h ▸ hns) := by
  subst h; rfl

/-- The group homomorphism `(C • W).Point →+ W.Point` induced by the admissible change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun P := match P with
    | .zero => .zero
    | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
        ((variableChange_nonsingular_iff W C x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C h₁.1 h₂.1 hxy, variableChange_addX,
        variableChange_addY]

/-- `mapVariableChange` sends `(x, y)` to `(u²x + r, u³y + u²sx + t)`. -/
@[simp] lemma mapVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular_iff W C x y).mpr h) := by
  simp only [mapVariableChange]
  rfl

/-- The change of variables is injective on points: it is inverted by the change of variables
`C⁻¹`. -/
lemma mapVariableChange_injective : Function.Injective (mapVariableChange W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · rw [← zero_def, (mapVariableChange W C).map_zero, mapVariableChange_some] at h
    exact absurd h.symm (some_ne_zero _)
  · rw [← zero_def, (mapVariableChange W C).map_zero, mapVariableChange_some] at h
    exact absurd h (some_ne_zero _)
  · rw [mapVariableChange_some, mapVariableChange_some] at h
    simp only [some.injEq] at h ⊢
    obtain ⟨hX, hY⟩ := h
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact ⟨hx,
      mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx)⟩

/-- Applying the change of variables `C⁻¹` (transported along `C⁻¹ • C • W = W`) and then `C`
recovers the original point. -/
private lemma mapVariableChange_mapVariableChange_inv (P : W.toAffine.Point) :
    mapVariableChange W C (mapVariableChange (C • W) C⁻¹
      (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm P)) = P := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← zero_def, _root_.map_zero]
  · rw [cast_some, mapVariableChange_some, mapVariableChange_some]
    simp only [some.injEq, VariableChange.inv_def, Units.val_inv_eq_inv_val]
    constructor <;> field

/-- The group isomorphism `(C • W).Point ≃+ W.Point` induced by the admissible change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. It is `mapVariableChange` upgraded to an
equivalence; the inverse is the change of variables `C⁻¹`, not obtained from bijectivity via
choice. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point where
  __ := mapVariableChange W C
  invFun P := mapVariableChange (C • W) C⁻¹
    (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
      (inv_smul_smul C W).symm P)
  left_inv := Function.RightInverse.leftInverse_of_injective
    (mapVariableChange_mapVariableChange_inv W C) (mapVariableChange_injective W C)
  right_inv := mapVariableChange_mapVariableChange_inv W C

/-- `equivVariableChange` is `mapVariableChange` as a bijection: the two agree as functions, so
`mapVariableChange_some` computes both. -/
@[simp] lemma coe_equivVariableChange :
    ⇑(equivVariableChange W C) = ⇑(mapVariableChange W C) := by
  simp only [equivVariableChange]
  rfl

/-- The inverse of `equivVariableChange` is literally the change of variables `C⁻¹`, transported
along `C⁻¹ • C • W = W`. Not a `simp` lemma: it would rewrite the left-hand side of
`equivVariableChange_symm_some`, which is the normal form worth having. -/
lemma coe_equivVariableChange_symm :
    ⇑(equivVariableChange W C).symm = fun P ↦ mapVariableChange (C • W) C⁻¹
      (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm P) := by
  simp only [equivVariableChange]
  rfl

/-- The inverse of `equivVariableChange` acts on an affine point by the inverse change of
variables `C⁻¹`, sending `(x, y)` to `(u⁻²(x - r), u⁻³(y - sx + sr - t))`. -/
@[simp] lemma equivVariableChange_symm_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    (equivVariableChange W C).symm (.some x y h)
      = .some ((C⁻¹.u : F) ^ 2 * x + C⁻¹.r)
          ((C⁻¹.u : F) ^ 3 * y + (C⁻¹.u : F) ^ 2 * C⁻¹.s * x + C⁻¹.t)
          ((variableChange_nonsingular_iff (C • W) C⁻¹ x y).mpr
            ((inv_smul_smul C W).symm ▸ h)) := by
  simp only [coe_equivVariableChange_symm, cast_some, mapVariableChange_some]

end Point

end WeierstrassCurve.Affine

end
