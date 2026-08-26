/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Weierstrass normal forms survive a base change

Mathlib's `WeierstrassCurve.IsCharNeTwoNF` asserts `a₁ = a₃ = 0`, and its `NormalForms` file
proves a great deal from that hypothesis. What it does not record is that the condition is
preserved by `map` and `baseChange` — the coefficients of `W.map f` are the images of `W`'s, so a
vanishing coefficient stays vanishing.

That gap matters as soon as a statement is about a curve over `ℤ` and a point over `ℚ`, which is
the shape of the classical Nagell–Lutz theorem: the hypothesis is natural on the integral model,
while the point lives on the base change, and without these instances the class has to be
re-established by hand at every such crossing.

## Main results

* `WeierstrassCurve.isCharNeTwoNF_map`: `a₁ = a₃ = 0` is preserved by a ring hom.
* `WeierstrassCurve.isCharNeTwoNF_baseChange`: the same for a base change, which is the spelling
  consumers hold. Both are instances, so the crossing is silent.
* `WeierstrassCurve.y_eq_zero_of_order_two`: a point of order two has `y = 0`.
-/

public section

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

/-- **Characteristic-≠-2 normal form is preserved by a ring hom.** `(W.map f).a₁` is `f W.a₁`, and
a hom sends `0` to `0`, so the vanishing survives.

As an `instance`, this is what lets typeclass search carry `IsCharNeTwoNF` across `W.map f`: a
caller who has the hypothesis on `W` and a statement about `W.map f` needs no bridging term. -/
instance isCharNeTwoNF_map (f : R →+* S) [W.IsCharNeTwoNF] : (W.map f).IsCharNeTwoNF :=
  ⟨by simp, by simp⟩

/-- **Characteristic-≠-2 normal form is preserved by a base change.** This is
`isCharNeTwoNF_map` at `algebraMap R S`, stated separately because `baseChange` is the spelling a
caller holds and instance search does not unfold it. -/
instance isCharNeTwoNF_baseChange [Algebra R S] [W.IsCharNeTwoNF] :
    (W.baseChange S).IsCharNeTwoNF :=
  W.isCharNeTwoNF_map (algebraMap R S)

/-- **In characteristic-≠-2 normal form, a two-torsion point has `y = 0`.** Negation is
`(x, y) ↦ (x, -y)`, so a point equal to its own negative has `2y = 0`; cancelling `2` finishes it.

Nothing here sees `ℤ` or `ℚ`, and nothing needs `a₂ = 0`: the argument is the normal-form identity
plus the ability to cancel `2` in the point's own field, so those are exactly the hypotheses. -/
lemma y_eq_zero_of_order_two {F : Type*} [Field F] [DecidableEq F]
    {E : WeierstrassCurve F} [E.IsCharNeTwoNF] (h2F : (2 : F) ≠ 0)
    {x y : F} (hns : E.toAffine.Nonsingular x y)
    (h2 : addOrderOf (Affine.Point.some _ _ hns) = 2) : y = 0 := by
  have hP : (2 : ℕ) • (Affine.Point.some _ _ hns) = 0 := h2 ▸ addOrderOf_nsmul_eq_zero _
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at hP
  have hneg : E.toAffine.negY x y = -y := by
    simp [Affine.negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  have hy : 2 * y = 0 := by linear_combination hP.2.trans hneg
  exact (mul_eq_zero.mp hy).resolve_left h2F

end WeierstrassCurve
