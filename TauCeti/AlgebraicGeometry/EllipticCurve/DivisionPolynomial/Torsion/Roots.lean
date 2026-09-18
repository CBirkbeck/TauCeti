/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Integral
-- Proof-only: the two evaluation bridges `ψₙ = Ψₙ` and `Ψₙ ² = ΨSqₙ` on the curve.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Eval
-- Proof-only: a vanishing `ψₙ` annihilates the point, and conversely.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul
-- Proof-only: over an algebraically closed field every `x` is the abscissa of a point.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.IsAlgClosed

/-!
# The roots of `ΨSqₙ` are the abscissae of the nonzero `n`-torsion

`ΨSqₙ` is the square of the `n`-division polynomial, pushed down to a polynomial in `x` alone. Its
roots are exactly the `x`-coordinates of the affine points killed by `n`: one direction holds over
any field, the other needs the base field algebraically closed, so that the `y` completing a root
to a point exists.

This is the dictionary the `n`-torsion is counted through — the kernel of `[n]` maps to the roots
of `ΨSqₙ` two-to-one away from the `2`-torsion, which is what matches `#ker [n] = n ²` against
`deg preΨₙ`.

## Main results

* `WeierstrassCurve.eval_ΨSq_eq_zero_of_zsmul_eq_zero`: a torsion point is a root.
* `WeierstrassCurve.exists_zsmul_eq_zero_of_eval_ΨSq_eq_zero`: over an algebraically closed field,
  every root is one.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- **A torsion point is a root of `ΨSqₙ`**: `ψₙ` vanishes at a point killed by `n`, and `ΨSqₙ` at
the abscissa is the square of that value. -/
theorem eval_ΨSq_eq_zero_of_zsmul_eq_zero {n : ℤ} {x y : F}
    (hns : W.toAffine.Nonsingular x y)
    (htors : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0) :
    (W.ΨSq n).eval x = 0 := by
  have hψ : (W.ψ n).evalEval x y = 0 := evalEval_ψ_eq_zero_of_zsmul_eq_zero W hns n htors
  rw [← evalEval_Ψ_sq_eq_eval_ΨSq W hns.left n, ← evalEval_ψ_eq_evalEval_Ψ W hns.left n, hψ,
    zero_pow two_ne_zero]

/-- **Over an algebraically closed field every root of `ΨSqₙ` is the abscissa of an `n`-torsion
point.** Solving the Weierstrass equation for `y` gives a point, and `ΨSqₙ(x) = 0` makes `ψₙ`
vanish there, which annihilates it. -/
theorem exists_zsmul_eq_zero_of_eval_ΨSq_eq_zero [IsAlgClosed F] [W.IsElliptic] {n : ℤ} {x : F}
    (hx : (W.ΨSq n).eval x = 0) :
    ∃ y, ∃ hns : W.toAffine.Nonsingular x y,
      n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
  obtain ⟨y, hy⟩ := W.toAffine.exists_point_on_curve x
  have hns : W.toAffine.Nonsingular x y := Affine.equation_iff_nonsingular.mp hy
  refine ⟨y, hns, zsmul_eq_zero_of_evalEval_ψ_eq_zero W hns n ?_⟩
  have hsq : (W.ψ n).evalEval x y ^ 2 = 0 := by
    rw [evalEval_ψ_eq_evalEval_Ψ W hy n, evalEval_Ψ_sq_eq_eval_ΨSq W hy n, hx]
  exact pow_eq_zero_iff two_ne_zero |>.mp hsq

end WeierstrassCurve

end
