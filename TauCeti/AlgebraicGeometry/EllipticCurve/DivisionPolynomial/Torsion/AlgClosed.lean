/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Integral
-- Proof-only: the `y`-coordinate of a point with rational `x` is rational.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.IsAlgClosed
-- Proof-only: the absorption of integral elements by an algebraically closed field
-- (`IsIntegral.mem_range_algebraMap_of_minpoly_splits`).
import Mathlib.RingTheory.Adjoin.Field

/-!
# Torsion points over an algebraically closed field are already rational

Over an algebraically closed `F`, a torsion point of `W` with coordinates in an extension `Ω` has
its coordinates in `F`: the extension buys no new torsion.

Integrality of the `x`-coordinate holds over any base, so closedness is used for one thing only —
splitting the coordinate's minimal polynomial. That step is stated separately, from a splitting
hypothesis, with the algebraically closed case as its corollary.

## Main results

* `WeierstrassCurve.mem_range_x_of_zsmul_eq_zero_of_splits`: it lies in the image of `F` as soon
  as its minimal polynomial splits there — the only thing a hypothesis on the field has to supply.
* `WeierstrassCurve.mem_range_x_of_zsmul_eq_zero`: hence, over an algebraically closed one, it
  lies in the image of `F`.
* `WeierstrassCurve.mem_range_baseChange_of_zsmul_eq_zero`: hence an `n`-torsion point of `W` over
  `Ω` is the base change of one over `F`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
  {Ω : Type*} [Field Ω] [Algebra F Ω]

/-- **The `x`-coordinate of a torsion point is rational as soon as its minimal polynomial splits.**
Integrality of the coordinate holds over any base; splitting is the only thing a hypothesis on the
field has to supply, and it is what puts the coordinate in the image of `F`. -/
theorem mem_range_x_of_zsmul_eq_zero_of_splits {n : ℤ} (hn : n ≠ 0) {x y : Ω}
    (hns : (W.baseChange Ω).toAffine.Nonsingular x y)
    (htors : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0)
    (hsplits : ((minpoly F x).map (algebraMap F F)).Splits) :
    x ∈ Set.range (algebraMap F Ω) :=
  (isIntegral_x_of_zsmul_eq_zero W hn hns htors).mem_range_algebraMap_of_minpoly_splits hsplits

variable [IsAlgClosed F]

/-- **The `x`-coordinate of a torsion point is rational** when the base field is algebraically
closed: every minimal polynomial splits there, so `mem_range_x_of_zsmul_eq_zero_of_splits`
applies. -/
theorem mem_range_x_of_zsmul_eq_zero {n : ℤ} (hn : n ≠ 0) {x y : Ω}
    (hns : (W.baseChange Ω).toAffine.Nonsingular x y)
    (htors : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0) :
    x ∈ Set.range (algebraMap F Ω) :=
  mem_range_x_of_zsmul_eq_zero_of_splits W hn hns htors
    (by simpa using IsAlgClosed.splits (minpoly F x))

/-- **A torsion point over an extension of an algebraically closed field is already rational.**
No field extension of an algebraically closed `F` buys new torsion: the coordinates of a torsion
point are integral over `F`, hence already in it. So the `n`-torsion of `W` over `Ω` is the base
change of the `n`-torsion over `F`, for every extension `Ω` and not only an algebraic one. -/
theorem mem_range_baseChange_of_zsmul_eq_zero [DecidableEq F] [DecidableEq Ω] {n : ℤ}
    (hn : n ≠ 0)
    {P : (W.baseChange Ω).toAffine.Point} (h : n • P = 0) :
    P ∈ Set.range (Affine.Point.baseChange (W' := W) F Ω) := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact ⟨0, Affine.Point.map_zero _⟩
  · have hJac : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
      have h' := congrArg (Jacobian.Point.toAffineAddEquiv (W.baseChange Ω)).symm h
      rw [map_zsmul, map_zero] at h'
      simpa using h'
    obtain ⟨x₀, hx₀⟩ := W.mem_range_x_of_zsmul_eq_zero hn hns hJac
    obtain ⟨y₀, hy₀⟩ := W.mem_range_y_of_equation_of_mem_range_x hns.left hx₀
    subst hx₀
    subst hy₀
    refine ⟨Affine.Point.some x₀ y₀ ((W.toAffine.baseChange_nonsingular
      (f := Algebra.ofId F Ω) (FaithfulSMul.algebraMap_injective F Ω) x₀ y₀).mp hns), ?_⟩
    rw [Affine.Point.map_some]
    simp only [Algebra.ofId_apply]

end WeierstrassCurve

end
