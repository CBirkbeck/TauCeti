/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on Weierstrass curves

Two facts about the invariants of an elliptic curve over a field, complementing
`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`:

* `WeierstrassCurve.a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero`: in characteristic `2`, an elliptic
  curve has `a₁ ≠ 0` or `a₃ ≠ 0`;
* `WeierstrassCurve.c₆_eq_zero_iff_j_eq_1728`: `c₆ = 0 ↔ j = 1728`, the analogue for `j = 1728`
  of Mathlib's `WeierstrassCurve.j_eq_zero_iff` (`j = 0 ↔ c₄ = 0`).

Both are consumed by the automorphism-group development in
`TauCeti/AlgebraicGeometry/EllipticCurve/Aut.lean`, the `Aut (E, O)` milestone of
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 1.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` at `d18b563029f3`, Apache 2.0,
by Kevin Buzzard and Claude).
-/

@[expose] public section

namespace WeierstrassCurve

variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- In characteristic `2`, an elliptic curve has `a₁ ≠ 0` or `a₃ ≠ 0`: otherwise `a₁ = a₃ = 0`
makes the partial derivative `∂/∂y = 2y + a₁x + a₃` vanish identically, so `Δ = 0`. -/
lemma a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero (h2 : (2 : K) = 0) : E.a₁ ≠ 0 ∨ E.a₃ ≠ 0 := by
  by_contra! h
  exact E.isUnit_Δ.ne_zero (by rw [Δ, b₈, b₆, b₄, b₂, h.1, h.2]; grobner)

/-- `c₆(E) = 0` if and only if `j(E) = 1728`, by the relation `1728·Δ = c₄³ - c₆²`. This is the
analogue for `j = 1728` of `WeierstrassCurve.j_eq_zero_iff` (`j = 0 ↔ c₄ = 0`). -/
lemma c₆_eq_zero_iff_j_eq_1728 : E.c₆ = 0 ↔ E.j = 1728 := by
  have h : E.c₆ ^ 2 = E.c₄ ^ 3 - 1728 * E.Δ := by linear_combination E.c_relation
  rw [← sq_eq_zero_iff, h, sub_eq_zero, j, Units.inv_mul_eq_iff_eq_mul, coe_Δ',
    mul_comm E.Δ 1728]

end WeierstrassCurve

end
