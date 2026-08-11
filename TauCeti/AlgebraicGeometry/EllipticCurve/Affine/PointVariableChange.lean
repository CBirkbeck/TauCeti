/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The isomorphism of point groups induced by a change of variables

Mathlib's affine `Point` API has `WeierstrassCurve.Affine.Point.map`, the group homomorphism
induced by a map of the base field for a *fixed* curve, but nothing for the isomorphism between
the point groups of two *different* curves related by an admissible change of variables. This file
supplies it: for `C : VariableChange F` over a field, `(x, y) ↦ (u²x + r, u³y + u²sx + t)` is a
group isomorphism `(C • W).Point ≃+ W.Point`.

## Main definitions

* `WeierstrassCurve.Affine.Point.mapVariableChange`: the group homomorphism
  `(C • W).Point →+ W.Point`.
* `WeierstrassCurve.Affine.Point.equivVariableChange`: the group isomorphism
  `(C • W).Point ≃+ W.Point`, whose inverse is the map induced by `C⁻¹` rather than an inverse
  extracted from bijectivity. Everything here is computable given `[DecidableEq F]`.
* `WeierstrassCurve.Affine.Point.mapVariableChange_some` and
  `WeierstrassCurve.Affine.Point.equivVariableChange_some`: what those two maps do to a point
  given by coordinates, both `@[simp]`.

Transport of the point group along an equality of curves — needed to use a `C • W = W'` fact on
points — is Mathlib's `AddEquiv.cast`, instantiated at `fun V ↦ V.toAffine.Point`; this file adds
no wrapper for it.

The route is the group-law formulae. Each of `negY`, `addX`, `negAddY`, `addY` and `slope`
transforms by an explicit power of `u` (`variableChange_negY` and its companions), and
`variableChange_equation` says the change of variables scales the Weierstrass polynomial by `u⁶`,
so it carries points to points. Those identities are what make the map additive.

## Implementation notes

`mapVariableChangeFun` and its equation lemmas, its injectivity, and the `AddEquiv.cast`
computation lemma are `private`: they are how the homomorphism is built, not part of what it
offers. The public surface is the two maps and their coordinate lemmas
`mapVariableChange_some` / `equivVariableChange_some`, both `@[simp]`, so a consumer never needs
to unfold anything.

That is also why the section is a plain `public section` rather than `@[expose]`. Exposing the
whole file would publish every proof body to make three `rfl`s go through, and it is incompatible
with the helpers being private — a public declaration may not refer to a private one, so the
exposed body of `mapVariableChange` would fail to elaborate with
`Unknown identifier 'mapVariableChangeFun'`. Routing the two public coordinate lemmas through the
private equation lemma removes the need for exposure entirely.

This is a prerequisite for `TauCetiRoadmap/EllipticCurves/README.md` §Layer 5's point isomorphism
for the quadratic twist: that statement is about the point groups of `E` and its twist, which
become isomorphic over `L` by a change of variables, and it cannot even be stated without the
isomorphism defined here.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` at the roadmap's pin
`bc2fe8ff7396`, FLT PR #1088, Apache 2.0). That file's own header reads
`Authors: Michael Stoll, Claude`. Following this repository's convention for adapted material, the
upstream authorship is credited here rather than in the copyright header.
-/

public section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-! ### Transformation of the group-law formulae under a change of variables

Throughout, the change of variables carries a point `(x, y)` of `C • W` to the point
`(u²x + r, u³y + u²sx + t)` of `W`. -/

lemma variableChange_negY (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) ^ 3 * (C • W).toAffine.negY x y + (C.u : F) ^ 2 * C.s * x + C.t := by
  simp [negY, variableChange_a₁, variableChange_a₃]
  field

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition (`negY`) only if the original pair does. -/
lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : F}
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

lemma variableChange_addX (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp [addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.negAddY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp [negAddY, addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_addY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

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
    rw [W.toAffine.slope_of_Y_ne rfl hΦy, (C • W).toAffine.slope_of_Y_ne rfl hy,
      ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
      div_eq_div_iff (sub_ne_zero.mpr hΦy) (sub_ne_zero.mpr hy)]
    simp [negY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
    field
  · have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
    rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hΦx
    have h2 := sub_ne_zero.mpr hx
    field

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`: the
change of variables scales the Weierstrass polynomial by `u⁶`. -/
lemma variableChange_equation (x y : F) :
    W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [equation_iff', variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val, field]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> linear_combination h

/-- **Nonsingularity transfers across the change of variables.** The two partial derivatives
transform by the matrix `![![u⁴, -su³], ![0, u³]]`, which is invertible because `u` is, so
`W_X ≠ 0 ∨ W_Y ≠ 0` holds at the image exactly when it holds at the source.

This is what lets the point map avoid `[W.IsElliptic]`: `equation_iff_nonsingular` would supply
nonsingularity from the equation, but only for an elliptic curve, whereas the isomorphism of point
groups holds for every Weierstrass curve over a field. -/
lemma variableChange_nonsingular (x y : F) :
    W.toAffine.Nonsingular ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Nonsingular x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  -- `W_Y` scales by `u³`
  have hY : 2 * ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
        + W.a₁ * ((C.u : F) ^ 2 * x + C.r) + W.a₃
      = (C.u : F) ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃) := by
    simp only [variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
    field
  -- `W_X` scales by `u⁴`, shifted by an `s`-multiple of `W_Y`
  have hX : W.a₁ * ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
        - (3 * ((C.u : F) ^ 2 * x + C.r) ^ 2 + 2 * W.a₂ * ((C.u : F) ^ 2 * x + C.r) + W.a₄)
      = (C.u : F) ^ 4 * ((C • W).a₁ * y - (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄))
        - C.s * ((C.u : F) ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃)) := by
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      Units.val_inv_eq_inv_val]
    field
  rw [nonsingular_iff', nonsingular_iff', variableChange_equation]
  refine and_congr_right fun _ ↦ ?_
  rw [hX, hY, ← not_and_or, ← not_and_or]
  refine not_congr ⟨fun ⟨h1, h2⟩ ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have hB := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 3 hu)
    rw [hB, mul_zero, mul_zero, sub_zero] at h1
    exact ⟨(mul_eq_zero.mp h1).resolve_left (pow_ne_zero 4 hu), hB⟩
  · exact ⟨by rw [h1, h2]; ring, by rw [h2]; ring⟩

/-! ### The induced isomorphism of point groups -/

namespace Point

/-- The underlying map `(C • W).Point → W.Point` of the change of variables, sending `0` to `0` and
`(x, y)` to `(u²x + r, u³y + u²sx + t)`. -/
private def mapVariableChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ((variableChange_nonsingular W C x y).mpr h)

@[simp] private lemma mapVariableChangeFun_zero : mapVariableChangeFun W C 0 = 0 := rfl

private lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := rfl

private lemma mapVariableChangeFun_injective :
    Function.Injective (mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [mapVariableChangeFun] at h
  · simp [mapVariableChangeFun] at h
  · rw [mapVariableChangeFun_some, mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    simp only [some.injEq]
    exact ⟨hx,
      mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx)⟩

variable [DecidableEq F] [W.IsElliptic]

/-! From here on `[W.IsElliptic]` is unavoidable: Mathlib puts the `AddCommGroup` structure on
`Point` under that hypothesis (`Affine/Point.lean`, the section opened by
`variable [Nontrivial R] [W'.IsElliptic]`), so without it `(C • W).Point` is not an additive group
and the statements below do not even typecheck. Everything above — the transformation laws, the
underlying map and its injectivity — holds for an arbitrary Weierstrass curve over a field. -/

/-- What Mathlib's `AddEquiv.cast` — transport of the point group along an equality of Weierstrass
curves — does to a point given by coordinates. The equiv itself is `AddEquiv.cast` and is not
restated here; only its value needs a name, since Mathlib states `cast` through `Equiv.cast` and
so gives no equation for it. -/
-- not `@[simp]`: Mathlib's `AddEquiv.cast_apply` is itself a simp lemma and rewrites this
-- left-hand side to the raw `cast` first, so `simpNF` reports the statement is not in
-- simp-normal form and the lemma could never fire. It is used by `rw` below, which is syntactic.
private lemma cast_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point) h (some x y hns)
      = some x y (h ▸ hns) := by
  subst h; rfl

/-- The group homomorphism `(C • W).Point →+ W.Point` induced by the admissible change of variables
`(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := equation_iff_nonsingular.mpr h₁
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := equation_iff_nonsingular.mpr h₂
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, mapVariableChangeFun_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C e₁ e₂ hxy, variableChange_addX, variableChange_addY]

/-- The group isomorphism `(C • W).Point ≃+ W.Point` induced by the admissible change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`, with inverse coming from `C⁻¹`. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, mapVariableChangeFun W C
      (mapVariableChangeFun (C • W) C⁻¹
        (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
          (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · have hz : (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm) 0 = 0 := _root_.map_zero _
      rw [← zero_def, hz, mapVariableChangeFun_zero, mapVariableChangeFun_zero]
    · rw [cast_some, mapVariableChangeFun_some, mapVariableChangeFun_some]
      simp only [some.injEq]
      refine ⟨?_, ?_⟩ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := mapVariableChangeFun W C
    invFun := fun P ↦ mapVariableChangeFun (C • W) C⁻¹
      (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (mapVariableChange W C).map_add' }

@[simp] lemma equivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    equivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) :=
  mapVariableChangeFun_some W C h

/-- What the group homomorphism does to a point given by coordinates. Stated separately from
`equivVariableChange_some` because a consumer holding a `→+` should not have to know that it is
the underlying map of an `≃+`. -/
@[simp] lemma mapVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) :=
  mapVariableChangeFun_some W C h

end Point

end WeierstrassCurve.Affine

end
