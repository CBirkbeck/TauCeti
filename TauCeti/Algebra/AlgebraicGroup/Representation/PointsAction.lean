/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.Coalgebra.Comodule.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The points action of a comodule

A right comodule `V` over a bialgebra `H` makes the `A`-points of the corresponding
affine monoid act on the scalar extension `A ⊗[R] V`: a point `g : H →ₐ[R] A` acts by
pushing the coaction coefficients through `g`, `A`-linearly. The two comodule axioms
are exactly the two monoid-action laws: the counit law sends the convolution unit to
the identity, and coassociativity sends convolution products to composites. Over a
Hopf algebra the points form a group, so the action upgrades to linear automorphisms
via `MonoidHom.toHomUnits` — no antipode computation is needed.

This is the comodule-to-representation direction of the Layer 1 dictionary
"representations = comodules": it realizes a comodule as an action of the functor of
points on scalar extensions of `V`.

## Main declarations

* `TauCeti.Comodule.endOfPoint`: the endomorphism of `A ⊗[R] V` attached to a point.
* `TauCeti.Comodule.pointsEndHom`: the action, as a monoid homomorphism from the
  convolution monoid of points to the endomorphism monoid.
* `TauCeti.Comodule.pointsAction`: over a Hopf algebra, the action by linear
  automorphisms.
-/

public section

namespace TauCeti

namespace Comodule

open Coalgebra WithConv TensorProduct

variable {R H V A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V]
  [CommSemiring A] [Algebra R A]

variable (V) in
/-- The endomorphism of the scalar extension `A ⊗[R] V` attached to an `A`-point of
the bialgebra: push the coaction coefficients through the point. -/
noncomputable def endOfPoint (g : H →ₐ[R] A) : A ⊗[R] V →ₗ[A] A ⊗[R] V :=
  LinearMap.liftBaseChange A
    ((TensorProduct.comm R V A).toLinearMap ∘ₗ
      LinearMap.lTensor V g.toLinearMap ∘ₗ coact (R := R) (C := H))

variable (V) in
@[simp]
lemma endOfPoint_tmul (g : H →ₐ[R] A) (a : A) (v : V) :
    endOfPoint V g (a ⊗ₜ[R] v) =
      a • TensorProduct.comm R V A (LinearMap.lTensor V g.toLinearMap (coact v)) := by
  simp [endOfPoint]

variable (V) in
/-- The convolution unit acts as the identity: the counit law of the comodule. -/
lemma endOfPoint_ofConv_one :
    endOfPoint V ((1 : WithConv (H →ₐ[R] A)).ofConv) = LinearMap.id := by
  apply LinearMap.restrictScalars_injective R
  refine TensorProduct.ext' fun a v => ?_
  have hlin : ((1 : WithConv (H →ₐ[R] A)).ofConv).toLinearMap =
      Algebra.linearMap R A ∘ₗ counit := by
    have h := AlgHom.toLinearMap_convOne (R := R) (C := H) (A := A)
    rw [LinearMap.convOne_def] at h
    exact toConv_injective h
  have hcomp : LinearMap.lTensor V ((1 : WithConv (H →ₐ[R] A)).ofConv).toLinearMap ∘ₗ
      coact (R := R) (C := H) =
      LinearMap.lTensor V (Algebra.linearMap R A) ∘ₗ (TensorProduct.mk R V R).flip 1 := by
    rw [hlin, LinearMap.lTensor_comp, LinearMap.comp_assoc, lTensor_counit_comp_coact]
  have hv := DFunLike.congr_fun hcomp v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply,
    map_one] at hv
  simp [endOfPoint_tmul, hv, TensorProduct.smul_tmul', smul_eq_mul]

omit [Comodule R H V] in
/-- The coact-free shuffle underlying `endOfPoint_ofConv_mul`: with the two coaction
columns already peeled off, the two ways of multiplying the pushed coefficients agree,
by commutativity of the value algebra. -/
private lemma shuffle (g h : WithConv (H →ₐ[R] A)) :
    (TensorProduct.lift ((Algebra.lsmul R R (A ⊗[R] V)).toLinearMap)).comp
        ((TensorProduct.comm R (A ⊗[R] V) A).toLinearMap.comp
          ((TensorProduct.map (TensorProduct.comm R V A).toLinearMap LinearMap.id).comp
            ((TensorProduct.map (LinearMap.lTensor V (g.ofConv).toLinearMap)
                LinearMap.id).comp
              (LinearMap.lTensor (V ⊗[R] H) (h.ofConv).toLinearMap)))) =
      (TensorProduct.comm R V A).toLinearMap.comp
        ((LinearMap.lTensor V (LinearMap.mul' R A)).comp
          ((LinearMap.lTensor V
              (TensorProduct.map (g.ofConv).toLinearMap (h.ofConv).toLinearMap)).comp
            (TensorProduct.assoc R V H H).toLinearMap)) := by
  refine TensorProduct.ext (TensorProduct.ext' fun w x => LinearMap.ext fun y => ?_)
  simp [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul, mul_comm]

/-- Restricting the endomorphism of a point along the flip is scalar collapse against
the one-column form of the action: the pure-tensor characterization of `endOfPoint`,
as a composite. -/
private lemma endOfPoint_comp_comm (g : WithConv (H →ₐ[R] A)) :
    (endOfPoint V g.ofConv).restrictScalars R ∘ₗ (TensorProduct.comm R V A).toLinearMap =
      (TensorProduct.lift ((Algebra.lsmul R R (A ⊗[R] V)).toLinearMap)).comp
        ((TensorProduct.comm R (A ⊗[R] V) A).toLinearMap.comp
          (TensorProduct.map
            ((TensorProduct.comm R V A).toLinearMap.comp
              ((LinearMap.lTensor V (g.ofConv).toLinearMap).comp
                (coact (R := R) (C := H))))
            LinearMap.id)) := by
  refine TensorProduct.ext' fun w c => ?_
  simp [endOfPoint_tmul, Algebra.lsmul_coe]

/-- Peeling the coaction column off `map (pre g) id`: the two-column form of the
`g`-leg against an untouched `h`-coefficient leg. Pure-tensor identity; the inner
coaction value rides through opaquely. -/
private lemma map_comp_lTensor (g h : WithConv (H →ₐ[R] A)) :
    TensorProduct.map
        ((TensorProduct.comm R V A).toLinearMap.comp
          ((LinearMap.lTensor V (g.ofConv).toLinearMap).comp (coact (R := R) (C := H))))
        LinearMap.id ∘ₗ
      LinearMap.lTensor V (h.ofConv).toLinearMap =
    (TensorProduct.map (TensorProduct.comm R V A).toLinearMap LinearMap.id).comp
        ((TensorProduct.map (LinearMap.lTensor V (g.ofConv).toLinearMap)
            LinearMap.id).comp
          (LinearMap.lTensor (V ⊗[R] H) (h.ofConv).toLinearMap)) ∘ₗ
      (coact (R := R) (C := H) (M := V)).rTensor H := by
  refine TensorProduct.ext' fun w x => ?_
  simp

variable (V) in
/-- Convolution products act as composites: the coassociativity law of the comodule. -/
lemma endOfPoint_ofConv_mul (g h : WithConv (H →ₐ[R] A)) :
    endOfPoint V ((g * h).ofConv) = endOfPoint V g.ofConv ∘ₗ endOfPoint V h.ofConv := by
  have hmul : ((g * h).ofConv).toLinearMap =
      LinearMap.mul' R A ∘ₗ
        TensorProduct.map (g.ofConv).toLinearMap (h.ofConv).toLinearMap ∘ₗ comul := by
    have hb := AlgHom.toLinearMap_convMul g h
    rw [LinearMap.convMul_def] at hb
    exact toConv_injective hb
  apply LinearMap.restrictScalars_injective R
  refine TensorProduct.ext' fun a v => ?_
  -- the endomorphism of the point `g`, evaluated on the flip of the `h`-column
  have c1 := DFunLike.congr_fun (endOfPoint_comp_comm (V := V) g)
    (LinearMap.lTensor V (h.ofConv).toLinearMap (coact (R := R) (C := H) v))
  -- peel the coaction column off the `g`-leg
  have c2 := DFunLike.congr_fun (map_comp_lTensor (V := V) g h) (coact (R := R) (C := H) v)
  -- the coact-free shuffle at the doubled coaction
  have c3 := DFunLike.congr_fun (shuffle (V := V) g h)
    ((coact (R := R) (C := H) (M := V)).rTensor H (coact (R := R) (C := H) v))
  -- coassociativity, valuewise
  have c4 := DFunLike.congr_fun (coassoc (R := R) (C := H) (M := V)) v
  -- fold the convolution product back together, valuewise at the coaction
  have c5 := DFunLike.congr_fun
    (congrArg (LinearMap.lTensor V) hmul) (coact (R := R) (C := H) v)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_toLinearMap] at c1 c2 c3 c4 c5
  rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp] at c5
  simp only [LinearMap.coe_comp, Function.comp_apply] at c5
  simp only [LinearMap.restrictScalars_apply, LinearMap.coe_comp, Function.comp_apply,
    endOfPoint_tmul, map_smul, c1, c2, c3, c4, c5]

variable (V) in
/-- The points action of a comodule, as a monoid homomorphism from the convolution
monoid of points to the endomorphism monoid of the scalar extension. -/
noncomputable def pointsEndHom :
    WithConv (H →ₐ[R] A) →* Module.End A (A ⊗[R] V) where
  toFun g := endOfPoint V g.ofConv
  map_one' := endOfPoint_ofConv_one V
  map_mul' g h := endOfPoint_ofConv_mul V g h

variable (V) in
@[simp]
lemma pointsEndHom_apply (g : WithConv (H →ₐ[R] A)) :
    pointsEndHom V g = endOfPoint V g.ofConv := by
  -- `pointsEndHom` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change endOfPoint V g.ofConv = _
  rfl

section Hopf

variable {R H V A : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V]
  [CommSemiring A] [Algebra R A]

variable (V) in
/-- Over a Hopf algebra the points act by linear automorphisms of the scalar
extension: the group of points lands in the units of the endomorphism monoid, with
inverses provided by the group structure rather than by an antipode computation. -/
noncomputable def pointsAction :
    WithConv (H →ₐ[R] A) →* ((A ⊗[R] V) ≃ₗ[A] (A ⊗[R] V)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[R] V)).toMonoidHom.comp
    (pointsEndHom V).toHomUnits

variable (V) in
@[simp]
lemma pointsAction_toLinearMap (g : WithConv (H →ₐ[R] A)) :
    (pointsAction V g : A ⊗[R] V →ₗ[A] A ⊗[R] V) = endOfPoint V g.ofConv := by
  -- `pointsAction` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change ((LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[R] V))
    ((pointsEndHom V).toHomUnits g) : A ⊗[R] V →ₗ[A] A ⊗[R] V) = _
  rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  rfl

end Hopf

end Comodule

end TauCeti
