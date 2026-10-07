/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IsTensorProduct

/-!
# Algebra homomorphisms out of a pushout over the base change

Let `S'` be the pushout of `R → S` along `R → R'`, as expressed by `Algebra.IsPushout R S R' S'`.
Mathlib's `Algebra.pushoutDesc` describes the `R`-algebra homomorphisms out of `S'`. This file
describes the `R'`-algebra homomorphisms out of `S'`: they are determined by their restrictions to
`S`, and every `R`-algebra homomorphism out of `S` extends to one. It also records the naturality
of `Algebra.IsPushout.cancelBaseChangeAlg` in the coefficient algebra.

## Main definitions

* `Algebra.IsPushout.lift f`: the `R'`-algebra homomorphism `S' →ₐ[R'] A` extending an
  `R`-algebra homomorphism `f : S →ₐ[R] A` along `S → S'`.

## Main results

* `Algebra.IsPushout.lift_algebraMap`: `lift f` restricts to `f` on `S`.
* `Algebra.IsPushout.algHom_ext'`: `R'`-algebra homomorphisms out of `S'` agreeing on `S` are
  equal.
* `Algebra.IsPushout.cancelBaseChangeAlg_symm_lTensor`: the isomorphism
  `S ⊗[R] T ≃ₐ[S] S' ⊗[R'] T` is natural in the `R'`-algebra `T`.
-/

public section

open scoped TensorProduct

namespace Algebra.IsPushout

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
  [Algebra R R'] [Algebra R' S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R R' S']
  [IsScalarTower R S S'] [IsPushout R S R' S']

section Lift

variable {A : Type*} [Semiring A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]

variable (R') in
/-- The `R'`-algebra homomorphism out of the pushout `S'` extending an `R`-algebra homomorphism
`f : S →ₐ[R] A` along `S → S'`. -/
noncomputable def lift (f : S →ₐ[R] A) : S' →ₐ[R'] A :=
  { pushoutDesc S' f (IsScalarTower.toAlgHom R R' A) fun x y ↦ (Algebra.commutes y (f x)).symm with
    commutes' := pushoutDesc_right S' f _ _ }

/-- `lift R' f` restricts to `f` on `S`. -/
@[simp]
theorem lift_algebraMap (f : S →ₐ[R] A) (s : S) : lift R' f (algebraMap S S' s) = f s := by
  unfold lift
  exact pushoutDesc_left S' f _ _ s

/-- Two `R'`-algebra homomorphisms out of the pushout `S'` that agree on `S` are equal. -/
theorem algHom_ext' {f g : S' →ₐ[R'] A}
    (h : (f.restrictScalars R).comp (IsScalarTower.toAlgHom R S S') =
      (g.restrictScalars R).comp (IsScalarTower.toAlgHom R S S')) : f = g :=
  AlgHom.restrictScalars_injective R <| IsPushout.algHom_ext (R' := R') S' (by ext; simp) h

end Lift

variable (S') in
/-- The isomorphism `S ⊗[R] T ≃ₐ[S] S' ⊗[R'] T` is natural in the `R'`-algebra `T`. -/
theorem cancelBaseChangeAlg_symm_lTensor {T T' : Type*} [CommRing T] [Algebra R' T]
    [Algebra R T] [IsScalarTower R R' T] [CommRing T'] [Algebra R' T'] [Algebra R T']
    [IsScalarTower R R' T'] (g : T →ₐ[R'] T') (z : S ⊗[R] T) :
    (cancelBaseChangeAlg R S R' S' T').symm
        (Algebra.TensorProduct.lTensor (S := S) S (g.restrictScalars R) z) =
      Algebra.TensorProduct.lTensor (S := S') S' g ((cancelBaseChangeAlg R S R' S' T).symm z) := by
  induction z <;> simp [*]

end Algebra.IsPushout
