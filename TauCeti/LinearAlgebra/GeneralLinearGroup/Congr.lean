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
`LinearMap.GeneralLinearGroup.congrLinearEquiv : GL R₁ M₁ ≃* GL R₂ M₂`, and identifies `GL R M` with
the automorphisms `M ≃ₗ[R] M` through `LinearMap.GeneralLinearGroup.generalLinearEquiv`. Groups of
linear automorphisms cut out by a structure they preserve — an orthogonal group, an isometry
group — are subgroups of `M ≃ₗ[R] M` rather than of `GL R M`, so what they need is the composite of
those two, which this file records as `LinearEquiv.congrAut`.

Conjugation needs no more than a semilinear equivalence, which is the generality
`congrLinearEquiv` already supplies: `e : M₁ ≃ₛₗ[σ₁₂] M₂` carries `R₁`-automorphisms of `M₁` to
`R₂`-automorphisms of `M₂`, the scalars travelling along `σ₁₂`. The two inverse-pair assumptions
give a round trip on each scalar ring — `σ₂₁ ∘ σ₁₂` is the identity on `R₁` and `σ₁₂ ∘ σ₂₁` the
identity on `R₂` — and it is the latter that makes the conjugate `R₂`-linear.

## Main definitions

* `LinearEquiv.congrAut`: conjugation by `e : M₁ ≃ₛₗ[σ₁₂] M₂`, as an isomorphism
  `(M₁ ≃ₗ[R₁] M₁) ≃* (M₂ ≃ₗ[R₂] M₂)`.
-/

public section

namespace TauCeti

section

open LinearMap.GeneralLinearGroup

variable {R₁ R₂ M₁ M₂ : Type*} [Semiring R₁] [Semiring R₂]
  [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid M₂] [Module R₂ M₂]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- Conjugation by a semilinear equivalence `e : M₁ ≃ₛₗ[σ₁₂] M₂`, as an isomorphism of automorphism
groups: Mathlib's `LinearMap.GeneralLinearGroup.congrLinearEquiv` read through
`LinearMap.GeneralLinearGroup.generalLinearEquiv`.

The two evaluation lemmas below are its characteristic API. -/
def _root_.LinearEquiv.congrAut (e : M₁ ≃ₛₗ[σ₁₂] M₂) : (M₁ ≃ₗ[R₁] M₁) ≃* (M₂ ≃ₗ[R₂] M₂) :=
  ((generalLinearEquiv R₁ M₁).symm.trans (congrLinearEquiv e)).trans (generalLinearEquiv R₂ M₂)

/-- Conjugating `f` by `e` sends `m` to `e (f (e.symm m))`. -/
@[simp]
theorem _root_.LinearEquiv.congrAut_apply (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₗ[R₁] M₁) (m : M₂) :
    LinearEquiv.congrAut e f m = e (f (e.symm m)) := by
  rw [LinearEquiv.congrAut, MulEquiv.trans_apply, MulEquiv.trans_apply]
  -- `generalLinearEquiv` computes on coercions, not at the level of `M₁ ≃ₗ[R] M₁`, so its inverse
  -- law has to be transported across `toLinearEquiv` before `simp` can use it.
  have h : ((generalLinearEquiv R₁ M₁).symm f).toLinearEquiv = f := by
    ext x
    rw [coe_toLinearEquiv, ← coeFn_generalLinearEquiv]
    exact DFunLike.congr_fun ((generalLinearEquiv R₁ M₁).apply_symm_apply f) x
  simp only [congrLinearEquiv_apply, coeFn_generalLinearEquiv, coe_ofLinearEquiv,
    LinearEquiv.trans_apply, h]

/-- Conjugation by `e`, as an equality of linear equivalences: `congrAut e f` is `f` pre-composed
with `e.symm` and post-composed with `e`. This is the structural form; the pointwise
`congrAut_apply` is the same fact read at a point, and structural consumers (determinants, traces)
want this one. -/
theorem _root_.LinearEquiv.congrAut_eq (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₗ[R₁] M₁) :
    LinearEquiv.congrAut e f = (e.symm.trans f).trans e :=
  LinearEquiv.ext fun m => LinearEquiv.congrAut_apply e f m

/-- Inverse conjugation by `e`, as an equality of linear equivalences.

Proved by characterising the inverse rather than by unfolding `congrAut` a second time: applying
`congrAut e` to both sides reduces this to `congrAut_eq`, so the coercion transport across
`toLinearEquiv` is performed once, in `congrAut_apply`, and not again here. -/
theorem _root_.LinearEquiv.congrAut_symm_eq (e : M₁ ≃ₛₗ[σ₁₂] M₂) (g : M₂ ≃ₗ[R₂] M₂) :
    (LinearEquiv.congrAut e).symm g = (e.trans g).trans e.symm := by
  rw [MulEquiv.symm_apply_eq, LinearEquiv.congrAut_eq]
  exact LinearEquiv.ext fun m => by simp

/-- Inverse conjugation by `e` sends `m` to `e.symm (g (e m))`. -/
@[simp]
theorem _root_.LinearEquiv.congrAut_symm_apply (e : M₁ ≃ₛₗ[σ₁₂] M₂) (g : M₂ ≃ₗ[R₂] M₂) (m : M₁) :
    (LinearEquiv.congrAut e).symm g m = e.symm (g (e m)) := by
  rw [LinearEquiv.congrAut_symm_eq]
  simp

end

end TauCeti
