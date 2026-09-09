/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# Naturality of base-changed points

This file records the two naturality properties of
`AlgHom.baseChangePointsMulEquiv`. Base-changing a bialgebra from `k` to `K`
identifies `K`-algebra maps out of `K ⊗[k] A` with `k`-algebra maps out of `A`; this
identification is compatible with post-composition in the value algebra and with
pre-composition by morphisms of coordinate bialgebras.

These lemmas are part of the ReductiveGroups roadmap Layer 0 base-change target: after the
convolution group structure on points, the functor-of-points dictionary needs base change to
behave naturally in both the value algebra and the coordinate Hopf algebra.

Worked examples of base-changed groups can combine these generic lemmas with the corresponding
unbased points naturality calculation, avoiding duplicate example-specific wrappers around the
same base-change argument.

## Main declarations

* `AlgHom.mapValue_baseChangePointsMulEquiv`: base change of points commutes with
  post-composition in the value algebra.
* `AlgHom.baseChangePointsMulEquiv_mapDomain`: base change of points commutes with
  pre-composition in the coordinate bialgebra.

## References

This builds on Mathlib's tensor-product bialgebra map
`Bialgebra.TensorProduct.map`, Mathlib's algebra base-change adjunction
`AlgHom.liftEquiv`, and the Tau Ceti convolution-points API in
`TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic` and
`TauCeti.Algebra.AlgebraicGroup.Hopf.Map`.
-/

public section

open TensorProduct WithConv

namespace TauCeti

section

section MapValue

variable {k K A R S : Type*} [CommSemiring k] [CommSemiring K] [Semiring A]
variable [CommSemiring R] [CommSemiring S] [Algebra k K] [_root_.Bialgebra k A]
variable [Algebra K R] [Algebra k R] [IsScalarTower k K R]
variable [Algebra K S] [Algebra k S] [IsScalarTower k K S]

/-- Base change of points is natural in the value algebra.

Post-composing an `R`-valued point by a `K`-algebra homomorphism `φ : R →ₐ[K] S` and then
base-changing agrees with first base-changing the point and then post-composing by `φ`. -/
lemma _root_.AlgHom.mapValue_baseChangePointsMulEquiv (φ : R →ₐ[K] S)
    (f : WithConv (A →ₐ[k] R)) :
    AlgHom.mapValue (H := K ⊗[k] A) φ
        (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f) =
      AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := S)
        (AlgHom.mapValue (H := A) (φ.restrictScalars k) f) := by
  ext a
  simp [AlgHom.mapValue_apply]

/-- The inverse direction of base change is natural in the value algebra.

Restricting a post-composed base-changed point along `a ↦ 1 ⊗ a` agrees with
post-composing the restricted point. -/
lemma _root_.AlgHom.baseChangePointsMulEquiv_symm_mapValue (φ : R →ₐ[K] S)
    (f : WithConv (K ⊗[k] A →ₐ[K] R)) :
    (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := S)).symm
        (AlgHom.mapValue (H := K ⊗[k] A) φ f) =
      AlgHom.mapValue (H := A) (φ.restrictScalars k)
        ((AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f) := by
  ext a
  simp only [AlgHom.baseChangePointsMulEquiv_symm_apply, AlgHom.mapValue_apply, AlgHom.coe_comp,
    Function.comp_apply]
  rfl

end MapValue

section MapDomain

variable {k K A B R : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
variable [CommSemiring A] [Semiring B] [_root_.Bialgebra k A] [_root_.Bialgebra k B]
variable [CommSemiring R] [Algebra K R] [Algebra k R] [IsScalarTower k K R]

/-- Base change of points is natural in the coordinate bialgebra.

Pre-composing a `B`-point by a bialgebra morphism `φ : A →ₐc[k] B` and then base-changing
agrees with first base-changing the point and then pre-composing by the scalar extension
`K ⊗[k] A →ₐc[K] K ⊗[k] B`. -/
lemma _root_.AlgHom.baseChangePointsMulEquiv_mapDomain (φ : A →ₐc[k] B)
    (f : WithConv (B →ₐ[k] R)) :
    AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)
        (AlgHom.mapDomain (A := R) φ f) =
      AlgHom.mapDomain (A := R)
        (_root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K) φ)
        (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := B) (R := R) f) := by
  ext a
  simp [AlgHom.mapDomain_apply]

/-- Pointwise form of `AlgHom.baseChangePointsMulEquiv_mapDomain` on pure tensors. -/
@[simp]
lemma _root_.AlgHom.baseChangePointsMulEquiv_mapDomain_apply_tmul (φ : A →ₐc[k] B)
    (f : WithConv (B →ₐ[k] R)) (s : K) (a : A) :
    AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)
        (AlgHom.mapDomain (A := R) φ f) (s ⊗ₜ[k] a) =
      s • f.ofConv (φ a) := by
  rw [AlgHom.baseChangePointsMulEquiv_apply_tmul, AlgHom.mapDomain_apply_apply]

/-- The inverse direction of base change is natural in the coordinate bialgebra.

Restricting along `a ↦ 1 ⊗ a` after pre-composing with the scalar extension of `φ` agrees
with first restricting and then pre-composing by `φ`. -/
lemma _root_.AlgHom.baseChangePointsMulEquiv_symm_mapDomain (φ : A →ₐc[k] B)
    (f : WithConv (K ⊗[k] B →ₐ[K] R)) :
    (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm
        (AlgHom.mapDomain (A := R)
          (_root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K) φ) f) =
      AlgHom.mapDomain (A := R) φ
        ((AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := B) (R := R)).symm f) := by
  ext a
  simp only [AlgHom.baseChangePointsMulEquiv_symm_apply, AlgHom.mapDomain_apply_apply,
    _root_.Bialgebra.TensorProduct.map_tmul, _root_.BialgHom.id_apply]

/-- Pointwise form of `AlgHom.baseChangePointsMulEquiv_symm_mapDomain`. -/
@[simp]
lemma _root_.AlgHom.baseChangePointsMulEquiv_symm_mapDomain_apply (φ : A →ₐc[k] B)
    (f : WithConv (K ⊗[k] B →ₐ[K] R)) (a : A) :
    ((AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm
        (AlgHom.mapDomain (A := R)
          (_root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K) φ) f)).ofConv a =
      f.ofConv (1 ⊗ₜ[k] φ a) := by
  simp only [AlgHom.baseChangePointsMulEquiv_symm_apply, AlgHom.mapDomain_apply_apply,
    _root_.Bialgebra.TensorProduct.map_tmul, _root_.BialgHom.id_apply]

end MapDomain

end

end TauCeti
