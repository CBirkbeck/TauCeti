/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.Algebra.Polynomial.QuadraticDiscriminant

/-!
# The node polynomial of a Weierstrass curve

When a Weierstrass curve degenerates to a node, the two tangent directions there are the roots of
a quadratic, and the reduction is called *split* exactly when those roots are rational over the
residue field. Mathlib writes that quadratic out inline, in the very definition of
`WeierstrassCurve.HasSplitMultiplicativeReduction`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`, applied to `W.integralModel R`), but
gives it no name and proves nothing about it. This file names it `WeierstrassCurve.nodePoly` and
says when it splits, discharging the TODO recorded just above that class — *"add characterization
in terms of the discriminant when the characteristic is not 2"* — and adding the characteristic-
two counterpart. The remaining step, rewriting the class itself through these criteria, needs
`integralModel` and belongs to the minimal-model slice.

* `WeierstrassCurve.nodePoly` is `c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`, defined over any
  commutative ring;
* `WeierstrassCurve.nodePoly_discrim` computes its discriminant as `-c₄ c₆`. This is the number
  the twist lane needs: twisting by `(t, n)` scales `-c₄ c₆` by `(t² - 4n)⁵`, i.e. by the twisting
  parameter times a square, so twisting by the right square class moves the discriminant into the
  squares;
* `WeierstrassCurve.map_nodePoly` is naturality, `(W.map φ).nodePoly = W.nodePoly.map φ`. It is
  what lets the criteria below — stated for `W.nodePoly.map φ`, i.e. for the *reduction* of the
  node polynomial — be read as statements about the node polynomial of the reduced curve;
* `WeierstrassCurve.nodePoly_smul` and `WeierstrassCurve.nodePoly_map_splits_smul_iff`: a change
  of variables `(u, r, s, t)` transforms the node polynomial by the affine substitution
  `T ↦ u T + s` and the unit scalar `u⁻⁶`, so whether it splits is an isomorphism invariant. This
  is why split multiplicative reduction is a property of the curve and not of the equation;
* `WeierstrassCurve.nodePoly_map_splits_iff_isSquare` and
  `WeierstrassCurve.nodePoly_map_splits_iff_of_two_eq_zero`: the splitting criteria themselves,
  each under the hypothesis that `c₄` survives the map. Away from residue characteristic two it
  splits iff the image of `-c₄ c₆` is a square; in residue characteristic two, where that says
  nothing, iff an Artin-Schreier condition holds. Both come from the general quadratic criteria
  of `TauCeti/Algebra/Polynomial/QuadraticDiscriminant.lean`.

Nothing here assumes a valuation or a reduction: every statement is about a Weierstrass curve
over a commutative ring and a ring homomorphism to a field, so it applies to any reduction map
one later chooses. They advance
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists), whose headline
`exists_quadraticTwist_hasSplitMultiplicativeReduction` — a curve with nonsplit multiplicative
reduction acquires split reduction after a separable quadratic twist — is proved by feeding the
twist's scaling of `-c₄ c₆` into `nodePoly_map_splits_iff_isSquare`.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`, at the roadmap's pin `bc2fe8ff7396`,
FLT PR #1088, Apache 2.0): the node-polynomial block of
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`, together with
`splitPolynomial_discrim` from `FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`,
renamed here to `nodePoly_discrim` because `splitPolynomial` names no declaration. Those files'
headers read `Authors: Kevin Buzzard, William Coram, Claude` and `Authors: Kevin Buzzard, Claude`;
following this repository's convention for adapted material, the upstream authorship is credited
here rather than in the copyright header. Ported with the source's `@[expose]` dropped, and with
the minimal-model and multiplicative-reduction blocks of the source file left to the PR that
consumes them.
-/

public section

namespace WeierstrassCurve

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] {k : Type*} [Field k]

/-- The **node polynomial** `c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`, whose roots are the
slopes of the two tangent directions at the node of a multiplicative reduction. This is the
polynomial Mathlib writes out inline in `WeierstrassCurve.HasSplitMultiplicativeReduction`, whose
splitting over the residue field *is* that class's defining condition. -/
noncomputable def nodePoly (W : WeierstrassCurve A) : Polynomial A :=
  .C W.c₄ * .X ^ 2 + .C (W.a₁ * W.c₄) * .X - .C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

/-- The discriminant of the node polynomial is `-c₄ c₆`. Hence the tangent directions at the node
are rational over the residue field exactly when `-c₄ c₆` is a square there
(`nodePoly_map_splits_iff_isSquare`); twisting by `(t, n)` multiplies `-c₄ c₆` by
`(t² - 4n)⁵ = (t² - 4n)⁴ · (t² - 4n)`, i.e. by the twisting parameter up to a square. -/
theorem nodePoly_discrim (W : WeierstrassCurve A) :
    discrim W.c₄ (W.a₁ * W.c₄) (-(54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄))
      = -(W.c₄ * W.c₆) := by
  simp only [discrim, c₄, c₆, b₂, b₄, b₆]; ring

/-- The node polynomial is natural in the coefficient ring: it commutes with base change of the
Weierstrass equation along any ring homomorphism. -/
@[simp]
lemma map_nodePoly (φ : A →+* B) (W : WeierstrassCurve A) :
    (W.map φ).nodePoly = W.nodePoly.map φ := by
  simp only [nodePoly, WeierstrassCurve.map_c₄, WeierstrassCurve.map_a₁, WeierstrassCurve.map_b₂,
    WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, WeierstrassCurve.map_a₂, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_ofNat, map_add, map_sub, map_mul, map_ofNat]

/-- The reduced node polynomial, presented as a quadratic with an additive constant term — the
shape `C a * X ^ 2 + C b * X + C c` that the criteria of
`TauCeti/Algebra/Polynomial/QuadraticDiscriminant.lean` consume. -/
lemma nodePoly_map_eq_quadratic (φ : A →+* B) (W : WeierstrassCurve A) :
    W.nodePoly.map φ = .C (φ W.c₄) * .X ^ 2 + .C (φ (W.a₁ * W.c₄)) * .X
      + .C (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  simp only [nodePoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  rw [map_neg, sub_eq_add_neg]

/-- The image of `nodePoly_discrim` under a ring homomorphism, in the shape produced by the
quadratic criteria applied to `nodePoly_map_eq_quadratic`. -/
lemma map_nodePoly_discrim (φ : A →+* B) (W : WeierstrassCurve A) :
    discrim (φ W.c₄) (φ (W.a₁ * W.c₄)) (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄))
      = φ (-(W.c₄ * W.c₆)) := by
  rw [discrim, mul_neg, sub_neg_eq_add, ← map_pow, ← map_ofNat φ 4, ← map_mul, ← map_mul,
    ← map_add]
  exact congrArg φ (by simpa only [discrim, mul_neg, sub_neg_eq_add] using W.nodePoly_discrim)

/-- Under a change of variables `C = (u, r, s, t)`, the node polynomial transforms by the affine
substitution `T ↦ u T + s` and the unit scalar `u⁻⁶` — reflecting that the tangent slopes `λ`
transform as `λ ↦ (λ - s)/u`. Over a field this makes splitting invariant; see
`nodePoly_map_splits_smul_iff`. -/
lemma nodePoly_smul (W : WeierstrassCurve A) (C : VariableChange A) :
    (C • W).nodePoly = .C ((↑C.u⁻¹ : A) ^ 6)
      * W.nodePoly.comp (.C (↑C.u : A) * .X + .C C.s) := by
  have e2 : (↑C.u⁻¹ : A) ^ 6 * (↑C.u : A) ^ 2 = (↑C.u⁻¹ : A) ^ 4 := by
    have := congrArg (Units.val (α := A)) (by group : C.u⁻¹ ^ 6 * C.u ^ 2 = C.u⁻¹ ^ 4)
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have e1 : (↑C.u⁻¹ : A) ^ 6 * (↑C.u : A) = (↑C.u⁻¹ : A) ^ 5 := by
    have := congrArg (Units.val (α := A)) (by group : C.u⁻¹ ^ 6 * C.u = C.u⁻¹ ^ 5)
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have e2p : (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 6 * (algebraMap A (Polynomial A) ↑C.u) ^ 2
      = (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 4 := by
    rw [← map_pow, ← map_pow, ← map_mul, e2, map_pow]
  have e1p : (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 6 * algebraMap A (Polynomial A) ↑C.u
      = (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 5 := by
    rw [← map_pow, ← map_mul, e1, map_pow]
  simp only [nodePoly, c₄, variableChange_a₁, variableChange_a₂, variableChange_b₂,
    variableChange_b₄, variableChange_b₆, Polynomial.mul_comp, Polynomial.add_comp,
    Polynomial.sub_comp, Polynomial.C_comp, Polynomial.X_comp, pow_two, mul_add, add_mul,
    mul_sub, sub_mul]
  simp only [Polynomial.C_eq_algebraMap, map_mul, map_pow, map_sub, map_add, map_ofNat]
  linear_combination
    (-(algebraMap A (Polynomial A) W.b₂ ^ 2 - 24 * algebraMap A (Polynomial A) W.b₄) *
        Polynomial.X ^ 2) * e2p +
    (-(2 * (algebraMap A (Polynomial A) W.b₂ ^ 2 - 24 * algebraMap A (Polynomial A) W.b₄) *
            algebraMap A (Polynomial A) C.s +
          algebraMap A (Polynomial A) W.a₁ *
            (algebraMap A (Polynomial A) W.b₂ ^ 2 - 24 * algebraMap A (Polynomial A) W.b₄)) *
        Polynomial.X) * e1p

/-- **Invariance of the node polynomial's splitting under change of variables.** Since a change of
variables transforms the node polynomial by an affine substitution and a unit scalar
(`nodePoly_smul`), whether it splits over a field `k` is unchanged. This is what makes split
multiplicative reduction an isomorphism invariant rather than a property of the equation. -/
lemma nodePoly_map_splits_smul_iff (φ : A →+* k) (W : WeierstrassCurve A) (C : VariableChange A) :
    ((C • W).nodePoly.map φ).Splits ↔ (W.nodePoly.map φ).Splits := by
  have hu : φ (↑C.u : A) ≠ 0 := (RingHom.isUnit_map φ C.u.isUnit).ne_zero
  have hu6 : φ ((↑C.u⁻¹ : A) ^ 6) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero 6 (RingHom.isUnit_map φ C.u⁻¹.isUnit).ne_zero
  rw [nodePoly_smul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_C,
    Polynomial.splits_mul_iff_right (Polynomial.C_ne_zero.mpr hu6) (Polynomial.Splits.C _)]
  exact (Polynomial.splits_iff_comp_splits_of_natDegree_eq_one
    (Polynomial.natDegree_linear hu)).symm

/-- **Split criterion away from residue characteristic two.** Over a field `k` with `2 ≠ 0`, and
provided `c₄` does not die under `φ` — the condition that makes the reduced polynomial genuinely
quadratic, and which multiplicative reduction supplies — the node polynomial splits, i.e. the two
tangent directions at the node are `k`-rational, exactly when `φ (-(c₄ * c₆))`, the image of its
discriminant (`nodePoly_discrim`), is a square in `k`. This discharges Mathlib's TODO at
`Reduction.lean:315`, and is the tool that, applied to a quadratic twist via the scaling
`-c₄' c₆' = (t² - 4n)⁵ · (-c₄ c₆)`, turns a nonsplit reduction into a split one after twisting by
the right square class. -/
lemma nodePoly_map_splits_iff_isSquare [NeZero (2 : k)] (φ : A →+* k) (W : WeierstrassCurve A)
    (hc₄ : φ W.c₄ ≠ 0) :
    (W.nodePoly.map φ).Splits ↔ IsSquare (φ (-(W.c₄ * W.c₆))) := by
  rw [nodePoly_map_eq_quadratic, Polynomial.splits_quadratic_iff hc₄, map_nodePoly_discrim]

/-- **Split criterion in residue characteristic two.** Over a field `k` of characteristic `2`,
where the square-class criterion `nodePoly_map_splits_iff_isSquare` says nothing, the node
polynomial splits exactly when its Artin-Schreier invariant lies in the image of `z ↦ z² + z`.
Both `c₄` and `c₆` are required nonzero in `k`; together they force the linear coefficient
`a₁ c₄` to be nonzero as well, which is what makes the criterion applicable. -/
lemma nodePoly_map_splits_iff_of_two_eq_zero (h2 : (2 : k) = 0) (φ : A →+* k)
    (W : WeierstrassCurve A) (hc₄ : φ W.c₄ ≠ 0) (hc₆ : φ W.c₆ ≠ 0) :
    (W.nodePoly.map φ).Splits ↔ ∃ z, φ (W.a₁ * W.c₄) ^ 2 * (z ^ 2 + z)
      = φ W.c₄ * (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  have hb : φ (W.a₁ * W.c₄) ≠ 0 := by
    have h4 : (4 : k) = 0 := by linear_combination (2 : k) * h2
    have hAk := map_nodePoly_discrim φ W
    rw [discrim] at hAk
    intro h0
    refine neg_ne_zero.mpr (mul_ne_zero hc₄ hc₆) ?_
    rw [← map_mul, ← map_neg]
    linear_combination -hAk + φ (W.a₁ * W.c₄) * h0
      + φ W.c₄ * φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) * h4
  rw [nodePoly_map_eq_quadratic, Polynomial.splits_quadratic_iff_of_two_eq_zero h2 hc₄ hb]

end WeierstrassCurve

end
