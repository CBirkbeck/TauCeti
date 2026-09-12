/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Conjugating automorphism groups along a linear equivalence

Mathlib conjugates general linear groups with
`LinearMap.GeneralLinearGroup.congrLinearEquiv : GL R M₁ ≃* GL R M₂`, and identifies `GL R M` with
the automorphisms `M ≃ₗ[R] M` through `LinearMap.GeneralLinearGroup.generalLinearEquiv`. Groups of
linear automorphisms cut out by a structure they preserve — an orthogonal group, an isometry
group — are subgroups of `M ≃ₗ[R] M` rather than of `GL R M`, so what they need is the composite of
those two, which this file records as `LinearEquiv.autCongr`.

## Main definitions

* `LinearEquiv.autCongr`: conjugation by `e : M₁ ≃ₗ[R] M₂`, as an isomorphism
  `(M₁ ≃ₗ[R] M₁) ≃* (M₂ ≃ₗ[R] M₂)`.

## Main statements

* `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`: `toLinearEquiv` undoes
  `ofLinearEquiv`, which is what carries the inverse law of `generalLinearEquiv` across to
  `M ≃ₗ[R] M`.
-/

public section

namespace TauCeti

section

open LinearMap.GeneralLinearGroup

variable {R M M₁ M₂ : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₁]
  [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- `toLinearEquiv` undoes `ofLinearEquiv`: the automorphism underlying the invertible map built
from `f` is `f` itself. The mirror of Mathlib's `AlgEquiv.toLinearEquiv_ofLinearEquiv`. -/
@[simp]
theorem _root_.LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv (f : M ≃ₗ[R] M) :
    (ofLinearEquiv f).toLinearEquiv = f :=
  rfl

/-- Conjugation by a linear equivalence `e : M₁ ≃ₗ[R] M₂`, as an isomorphism of automorphism
groups: Mathlib's `LinearMap.GeneralLinearGroup.congrLinearEquiv` read through
`LinearMap.GeneralLinearGroup.generalLinearEquiv`.

The two evaluation lemmas below are its characteristic API. -/
def _root_.LinearEquiv.autCongr (e : M₁ ≃ₗ[R] M₂) : (M₁ ≃ₗ[R] M₁) ≃* (M₂ ≃ₗ[R] M₂) :=
  ((generalLinearEquiv R M₁).symm.trans (congrLinearEquiv e)).trans (generalLinearEquiv R M₂)

/-- Conjugating `f` by `e` sends `m` to `e (f (e.symm m))`. -/
@[simp]
theorem _root_.LinearEquiv.autCongr_apply_apply (e : M₁ ≃ₗ[R] M₂) (f : M₁ ≃ₗ[R] M₁) (m : M₂) :
    LinearEquiv.autCongr e f m = e (f (e.symm m)) := by
  rw [LinearEquiv.autCongr, MulEquiv.trans_apply, MulEquiv.trans_apply]
  -- `generalLinearEquiv` computes on coercions, not at the level of `M₁ ≃ₗ[R] M₁`, so its inverse
  -- law has to be transported across `toLinearEquiv` before `simp` can use it.
  have h : ((generalLinearEquiv R M₁).symm f).toLinearEquiv = f :=
    LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv f
  simp only [congrLinearEquiv_apply, coeFn_generalLinearEquiv, coe_ofLinearEquiv,
    LinearEquiv.trans_apply, h]

/-- Inverse conjugation by `e` sends `m` to `e.symm (g (e m))`. -/
@[simp]
theorem _root_.LinearEquiv.autCongr_symm_apply_apply (e : M₁ ≃ₗ[R] M₂) (g : M₂ ≃ₗ[R] M₂) (m : M₁) :
    (LinearEquiv.autCongr e).symm g m = e.symm (g (e m)) := by
  rw [LinearEquiv.autCongr, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply,
    congrLinearEquiv_symm]
  -- `generalLinearEquiv` computes on coercions, not at the level of `M₂ ≃ₗ[R] M₂`, so its inverse
  -- law has to be transported across `toLinearEquiv` before `simp` can use it.
  have h : ((generalLinearEquiv R M₂).symm g).toLinearEquiv = g :=
    LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv g
  simp only [congrLinearEquiv_apply, MulEquiv.symm_symm, coeFn_generalLinearEquiv,
    coe_ofLinearEquiv, LinearEquiv.symm_symm, LinearEquiv.trans_apply, h]

end

end TauCeti
