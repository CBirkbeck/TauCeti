/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
-- Proof-only: the norm over the polynomial ring, used for injectivity.
import Mathlib.RingTheory.Norm.Basic

/-!
# Evaluating the coordinate ring of a Weierstrass curve at a point

The coordinate ring `R[W]` of an affine Weierstrass curve `W` is `AdjoinRoot W.polynomial`, so at a
point `(x, y)` satisfying the Weierstrass equation the evaluation map `Polynomial.evalEval x y`
factors through it, by Mathlib's `AdjoinRoot.evalEval`. The same holds one level up: a point with
coordinates in an `R`-algebra `A` — that is, a solution of the equation of the base change `W⁄A` —
gives an `R`-algebra homomorphism `R[W] →ₐ[R] A`, and conversely every such homomorphism is
evaluation at the images of the two coordinate functions, which therefore solve that equation.
These statements concern the affine model `WeierstrassCurve.Affine R` itself, not a global
`WeierstrassCurve R`.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.evalAlgHom`: evaluation of the coordinate ring
  at a point of `W⁄A`, an `R`-algebra homomorphism into `A`.

## Main results

* `WeierstrassCurve.evalEval_eq_of_mk_eq`: bivariate polynomials that are equal in the
  coordinate ring evaluate equally at a point of the curve.
* `WeierstrassCurve.Affine.CoordinateRing.algHom_mk_eq_evalEval`: an algebra homomorphism
  out of the coordinate ring is evaluation at the images of the coordinate functions, and
  `WeierstrassCurve.Affine.CoordinateRing.equation_of_algHom` says that those images
  satisfy the Weierstrass equation of the base change.
* `WeierstrassCurve.Affine.CoordinateRing.algHom_ext`: two algebra homomorphisms out of
  the coordinate ring that agree on the two coordinate functions are equal.
* `WeierstrassCurve.Affine.CoordinateRing.algHom_injective`: over a field, an algebra
  homomorphism out of the coordinate ring under which `x` stays transcendental is injective. This
  is the nonconstancy criterion the isogeny development already used for pullbacks
  (`TauCeti.Isogeny.pullback_injective`, which is now this lemma applied to a pullback), stated
  once for an arbitrary algebra homomorphism.

Everything but the last result is stated over an arbitrary commutative ring; the curve need not be
elliptic, and `R` need not be a domain, since the statement is exactly the factorisation and
nothing more. `algHom_injective` needs a field, because the norm it argues with needs the rank-two
basis of `R[W]` over `R[X]`.

This supports the Nagell–Lutz route of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item
"The torsion subgroup and Nagell–Lutz", whose division-polynomial identities Mathlib states in the
coordinate ring but which are consumed at points of the curve. The converse evaluation statements
also support Layer 0's point–place dictionary by recovering an equation solution from a residue
degree-one ideal, and `evalAlgHom` together with `algHom_injective` is what Layer 0.5's
translations `τ_P` are built from: the pullback of `τ_P` is evaluation at a translate of the
generic point.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve.Affine R) {x y : R}

/-- Bivariate polynomials that are equal in the coordinate ring `R[W]` evaluate equally at a
point `(x, y)` of `W`. -/
theorem evalEval_eq_of_mk_eq (h : W.Equation x y) {p q : R[X][Y]}
    (hpq : Affine.CoordinateRing.mk W p = Affine.CoordinateRing.mk W q) :
    p.evalEval x y = q.evalEval x y := by
  have hev := AdjoinRoot.evalEval_mk (p := W.polynomial) h
  exact hev p ▸ hev q ▸ congrArg _ hpq

namespace Affine.CoordinateRing

variable {A : Type*} [CommRing A] [Algebra R A] {W : _root_.WeierstrassCurve.Affine R} {x y : A}

/-- **An algebra homomorphism out of the coordinate ring is evaluation at the images of the two
coordinate functions**, the coefficients of the polynomial being carried into the target algebra
first. -/
theorem algHom_mk_eq_evalEval (f : W.CoordinateRing →ₐ[R] A) (p : R[X][Y]) :
    f (CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap R A))).evalEval
        (f (CoordinateRing.mk W (C X)))
        (f (CoordinateRing.mk W Y)) := by
  -- `f` precomposed with the quotient map, as an `R`-algebra map on bivariate polynomials
  let g : R[X][Y] →ₐ[R] A :=
    f.comp ((AdjoinRoot.mkₐ W.polynomial).restrictScalars R)
  have hg (q : R[X][Y]) : g q = f (CoordinateRing.mk W q) := by
    simp only [g, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AdjoinRoot.coe_mkₐ]
  have key : g.toRingHom =
      (evalEvalRingHom (g (C X)) (g Y)).comp (mapRingHom (mapRingHom (algebraMap R A))) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext r
        have hCC : (C (C r) : R[X][Y]) = algebraMap R R[X][Y] r :=
          (congrFun coe_algebraMap_eq_CC r).symm
        simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_evalRingHom, eval_C]
        rw [hCC, g.commutes]
      · simp
    · simp
  rw [← hg]
  exact RingHom.congr_fun key p

/-- **The images of the coordinate functions under an algebra homomorphism out of the coordinate
ring satisfy the Weierstrass equation** of the base-changed curve. -/
theorem equation_of_algHom (f : W.CoordinateRing →ₐ[R] A) :
    (W.map (algebraMap R A)).toAffine.Equation
      (f (CoordinateRing.mk W (C X)))
      (f (CoordinateRing.mk W Y)) := by
  rw [Affine.Equation, Affine.map_polynomial,
    ← algHom_mk_eq_evalEval f W.polynomial, AdjoinRoot.mk_self, map_zero]

/-- **Two algebra homomorphisms out of the coordinate ring agreeing on the two coordinate
functions are equal**: the coordinate ring is generated by them. -/
@[ext]
theorem algHom_ext {f g : W.CoordinateRing →ₐ[R] A}
    (hX : f (CoordinateRing.mk W (C X)) =
      g (CoordinateRing.mk W (C X)))
    (hY : f (CoordinateRing.mk W Y) =
      g (CoordinateRing.mk W Y)) : f = g := by
  refine AlgHom.ext fun z ↦ ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [algHom_mk_eq_evalEval f p, algHom_mk_eq_evalEval g p, hX, hY]

/-- The coordinate-ring map underlying `evalAlgHom`, before it is packaged as an algebra
homomorphism: base change to `A`, then evaluate. -/
private noncomputable def evalRingHom
    (h : Polynomial.evalEval x y (W.map (algebraMap R A)).polynomial = 0) :
    W.CoordinateRing →+* A :=
  (AdjoinRoot.evalEval h).comp
    (CoordinateRing.map W (algebraMap R A))

private theorem evalRingHom_mk
    (h : Polynomial.evalEval x y (W.map (algebraMap R A)).polynomial = 0) (p : R[X][Y]) :
    evalRingHom h (CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap R A))).evalEval x y := by
  rw [evalRingHom, RingHom.comp_apply,
    CoordinateRing.map_mk, AdjoinRoot.evalEval_mk]

/-- **Evaluation of the coordinate ring at a point of the base-changed curve.** A solution
`(x, y)` of the Weierstrass equation of `W⁄A` is a point of `W` with coordinates in `A`, and
substituting it into a polynomial function factors through the coordinate ring. -/
noncomputable def evalAlgHom (h : (W.map (algebraMap R A)).toAffine.Equation x y) :
    W.CoordinateRing →ₐ[R] A where
  __ := evalRingHom h
  commutes' c := by
    have hc := evalRingHom_mk (h : Polynomial.evalEval x y _ = 0) (CC c)
    have hmk : CoordinateRing.mk W (CC c) =
        algebraMap R W.CoordinateRing c := by
      rw [IsScalarTower.algebraMap_apply R R[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq]
      (rfl)
    rw [hmk] at hc
    simpa using hc

/-- Evaluating the class of a polynomial in the coordinate ring is mapped polynomial evaluation
at the given solution of the Weierstrass equation. -/
@[simp]
theorem evalAlgHom_mk (h : (W.map (algebraMap R A)).toAffine.Equation x y) (p : R[X][Y]) :
    evalAlgHom h (CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap R A))).evalEval x y :=
  evalRingHom_mk h p

/-- Evaluation sends the coordinate-ring class of `X` to the first coordinate `x`. -/
theorem evalAlgHom_mk_C_X (h : (W.map (algebraMap R A)).toAffine.Equation x y) :
    evalAlgHom h (CoordinateRing.mk W (C X)) = x := by
  rw [evalAlgHom_mk]
  simp [evalEval_C]

/-- Evaluation sends the coordinate-ring class of `Y` to the second coordinate `y`. -/
theorem evalAlgHom_mk_Y (h : (W.map (algebraMap R A)).toAffine.Equation x y) :
    evalAlgHom h (CoordinateRing.mk W Y) = y := by
  rw [evalAlgHom_mk]
  simp

/-- The class of the coordinate `X` is the image of `X` under the structure map of the coordinate
ring over the polynomial ring. -/
theorem mk_C_X : CoordinateRing.mk W (C X) =
    algebraMap R[X] W.CoordinateRing X := by
  rw [AdjoinRoot.algebraMap_eq]
  (rfl)

section Field

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F}
  {A : Type*} [CommRing A] [Algebra F A]

/-- **An algebra homomorphism out of the coordinate ring under which the coordinate `x` stays
transcendental is injective.** A nonzero element of the kernel has nonzero norm over `F[x]`, and
that norm is a polynomial relation killing the image of `x`.

Over a field the coordinate ring is free of rank two over `F[X]`, which is what makes the norm
available; no ellipticity and no hypothesis on `A` beyond being an `F`-algebra is needed. -/
theorem algHom_injective (f : W.CoordinateRing →ₐ[F] A)
    (hx : Transcendental F (f (CoordinateRing.mk W (C X)))) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).2
  intro z hz
  by_contra hz₀
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq z
  set N : F[X] := Algebra.norm F[X] z with hN_def
  have hN₀ : N ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis
      (CoordinateRing.basis W)).2 hz₀
  have hnorm : algebraMap F[X] W.CoordinateRing N =
      z * CoordinateRing.mk W
        (C p + C q * (-(Y : F[X][Y]) - C (C W.a₁ * X + C W.a₃))) := by
    rw [hN_def, ← hpq]
    simpa [CoordinateRing.smul] using
      CoordinateRing.coe_norm_smul_basis (W' := W) p q
  refine hx ⟨N, hN₀, ?_⟩
  have hhom : Polynomial.aeval
      (f (CoordinateRing.mk W (C X))) =
      f.comp (IsScalarTower.toAlgHom F F[X] W.CoordinateRing) := by
    apply Polynomial.algHom_ext
    simp
  rw [AlgHom.congr_fun hhom N, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, hnorm, map_mul,
    hz, zero_mul]

end Field

end Affine.CoordinateRing

end WeierstrassCurve

end
