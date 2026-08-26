/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Unramified.Field

/-!
# The invariant differential of an elliptic curve

For an elliptic curve `E` over a field `F` this file constructs the invariant differential
`ω = dx / (2y + a₁x + a₃)` inside the module of Kähler differentials `Ω[K(E)/F]` of the
function field, and proves that it is nonzero.

The denominator is the image in `K(E)` of `polynomialY = W_Y`, the partial derivative of the
Weierstrass polynomial with respect to `Y`. It is nonzero for two separate reasons, and the
file proves both: `W_Y` is a nonzero *polynomial* — in characteristic two that is exactly where
`Δ ≠ 0` enters, since there `W_Y = a₁X + a₃` — and it has degree below `deg W`, so it
survives the passage to `F[E]` and then to `K(E)`.

That `D x ≠ 0` is the substantial half. The argument is by contradiction and is
characteristic-free: if `D x = 0` then `D` kills every polynomial in `x`, and differentiating
the Weierstrass relation `y² + (a₁x + a₃) y = x³ + a₂x² + a₄x + a₆` leaves
`(2y + a₁x + a₃) · D y = 0`. The denominator is invertible in the field `K(E)`, so `D y = 0` as
well; since `F[E]` is spanned by `1` and `y` over `F[x]` and `K(E)` is its fraction field, `D`
then vanishes identically. A vanishing differential module says `K(E)/F` is formally unramified,
hence separable algebraic, which contradicts `x` being transcendental over `F`.

## Main definitions

* `TauCeti.WeierstrassCurve.Affine.invariantDifferential`: the invariant differential `ω`, as an
  element of `Ω[K(E)/F]`.

## Main results

* `TauCeti.WeierstrassCurve.Affine.denom_ne_zero`: the denominator `2y + a₁x + a₃` is nonzero.
* `TauCeti.WeierstrassCurve.Affine.D_X_ne_zero`: `D x ≠ 0` in `Ω[K(E)/F]`.
* `TauCeti.WeierstrassCurve.Affine.invariantDifferential_ne_zero`: `ω ≠ 0`, which is the
  differential-form statement that `ω` has no zeros and no poles.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.5 and III.5.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Chris Birkbeck), Apache-2.0, file
`projects/HasseWeil/HasseWeil/InvariantDifferential.lean` at commit
`513e83879e2f`: `D_x_ne_zero`, `denom_ne_zero`, `invariantDifferential` and
`invariantDifferential_ne_zero`. The proofs are reorganised here: the source carried a
`maxHeartbeats` override on a single monolithic `D_x_ne_zero`, whose nested steps are separate
private lemmas below, and the source's `denom_ne_zero` argument, which it repeated verbatim inside
`D_x_ne_zero`, is proved once as `algebraMap_mk_polynomialY`.
-/

public section

open Polynomial Polynomial.Bivariate

namespace TauCeti

namespace WeierstrassCurve.Affine

open _root_.WeierstrassCurve _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] (E : _root_.WeierstrassCurve.Affine F)

/-! ### The denominator `2y + a₁x + a₃` -/

/-- The partial derivative `W_Y = 2Y + a₁X + a₃` of the Weierstrass polynomial is a nonzero
polynomial when `E` is elliptic. In characteristic two the first term vanishes, and it is `Δ ≠ 0`
that rules out `a₁ = a₃ = 0`. -/
private lemma polynomialY_ne_zero [E.IsElliptic] : E.polynomialY ≠ 0 := by
  intro h
  rw [_root_.WeierstrassCurve.Affine.polynomialY] at h
  have h1 := congr_arg (fun p => p.coeff 1) h
  have h0 := congr_arg (fun p => p.coeff 0) h
  simp only [map_add, map_mul, coeff_add, coeff_mul_X, coeff_C, ↓reduceIte, coeff_mul_C,
    zero_mul, add_zero, coeff_zero, map_eq_zero, mul_coeff_zero, coeff_X, one_ne_zero,
    mul_zero, zero_add] at h1 h0
  have ha1 : E.a₁ = 0 := by
    have := congr_arg (fun p => p.coeff 1) h0
    simp only [coeff_add, coeff_mul_X, coeff_C_zero, coeff_C_succ, add_zero, coeff_zero] at this
    exact this
  have ha3 : E.a₃ = 0 := by
    have := congr_arg (fun p => p.coeff 0) h0
    simp only [coeff_add, mul_coeff_zero, coeff_C_zero, coeff_X_zero, mul_zero, zero_add,
      coeff_zero] at this
    exact this
  refine absurd ((show _root_.WeierstrassCurve.Δ E = 0 by
    simp only [_root_.WeierstrassCurve.Δ]
    rw [show _root_.WeierstrassCurve.b₂ E = 0 by
        simp only [_root_.WeierstrassCurve.b₂, ha1]; linear_combination 2 * E.a₂ * h1,
      show _root_.WeierstrassCurve.b₄ E = 0 by
        simp only [_root_.WeierstrassCurve.b₄, ha1, ha3]; linear_combination E.a₄ * h1,
      show _root_.WeierstrassCurve.b₆ E = 0 by
        simp only [_root_.WeierstrassCurve.b₆, ha3]; linear_combination 2 * E.a₆ * h1]
    ring) ▸ E.isUnit_Δ) not_isUnit_zero

/-- `W_Y` stays nonzero in the coordinate ring: its degree is below `deg W`, so it is not a
multiple of `W`. -/
private lemma mk_polynomialY_ne_zero [E.IsElliptic] :
    _root_.WeierstrassCurve.Affine.CoordinateRing.mk E E.polynomialY ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (polynomialY_ne_zero E) <| by
    rw [natDegree_polynomial, _root_.WeierstrassCurve.Affine.polynomialY]
    have : (Polynomial.C (Polynomial.C (2 : F)) * (Y : F[X][Y])).natDegree ≤ 1 :=
      Polynomial.natDegree_mul_le.trans
        (by simp [Polynomial.natDegree_C, Polynomial.natDegree_X])
    exact Nat.lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
      (by rw [Polynomial.natDegree_C]; omega)

/-- The image of `W_Y` in the function field, written out as `2y + (a₁x + a₃)`. Both
`denom_ne_zero` and the differentiation step inside `D_X_ne_zero` need this identification; the
source proved it twice. -/
private lemma algebraMap_mk_polynomialY :
    algebraMap E.CoordinateRing E.FunctionField
        (_root_.WeierstrassCurve.Affine.CoordinateRing.mk E E.polynomialY) =
      2 * algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial) +
        algebraMap (Polynomial F) E.FunctionField
          (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) := by
  have hmk : (_root_.WeierstrassCurve.Affine.CoordinateRing.mk E E.polynomialY :
        E.CoordinateRing) =
      algebraMap (Polynomial F) E.CoordinateRing (Polynomial.C 2) * AdjoinRoot.root E.polynomial +
        algebraMap (Polynomial F) E.CoordinateRing
          (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) := by
    change AdjoinRoot.mk E.polynomial E.polynomialY = _
    rw [_root_.WeierstrassCurve.Affine.polynomialY, map_add, map_mul, AdjoinRoot.mk_X]
    rfl
  rw [hmk, map_add, map_mul,
    ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
    ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField]
  congr 1
  congr 1
  rw [show (Polynomial.C (2 : F) : Polynomial F) = algebraMap F (Polynomial F) 2 from rfl,
    ← IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField,
    show algebraMap F E.FunctionField (2 : F) = (2 : E.FunctionField) from by simp [map_ofNat]]

/-- The denominator, in the `F[X]`-form the differentiation step produces. -/
private lemma two_mul_root_add_ne_zero [E.IsElliptic] :
    2 * algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial) +
      algebraMap (Polynomial F) E.FunctionField
        (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) ≠ 0 := by
  rw [← algebraMap_mk_polynomialY]
  intro h
  exact mk_polynomialY_ne_zero E
    ((IsFractionRing.injective E.CoordinateRing E.FunctionField).eq_iff.mp
      (h.trans (map_zero _).symm))

/-- `a₁x + a₃` in the function field is the image of the polynomial `a₁X + a₃`. -/
private lemma algebraMap_a₁_mul_X_add_a₃ :
    algebraMap F E.FunctionField E.a₁ *
        algebraMap E.CoordinateRing E.FunctionField
          (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X) +
      algebraMap F E.FunctionField E.a₃ =
      algebraMap (Polynomial F) E.FunctionField
        (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) := by
  rw [map_add, map_mul,
    show algebraMap (Polynomial F) E.FunctionField (Polynomial.C E.a₁) =
        algebraMap F E.FunctionField E.a₁ from
      (IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField E.a₁).symm,
    show algebraMap (Polynomial F) E.FunctionField (Polynomial.C E.a₃) =
        algebraMap F E.FunctionField E.a₃ from
      (IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField E.a₃).symm,
    IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField]

/-- **The denominator of the invariant differential is nonzero.** `2y + a₁x + a₃` is the image
of `W_Y` in `K(E)`, and `W_Y` is a nonzero polynomial of degree below `deg W`, so it survives
both `F[X][Y] → F[E]` and `F[E] → K(E)`. -/
lemma denom_ne_zero [E.IsElliptic] :
    (2 : E.FunctionField) *
        algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial) +
      algebraMap F E.FunctionField E.a₁ *
        algebraMap E.CoordinateRing E.FunctionField
          (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X) +
      algebraMap F E.FunctionField E.a₃ ≠ 0 := by
  rw [add_assoc, algebraMap_a₁_mul_X_add_a₃]
  exact two_mul_root_add_ne_zero E

end WeierstrassCurve.Affine

end TauCeti
