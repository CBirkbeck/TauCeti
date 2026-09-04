/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Basic.Real.Basic

/-!
# The associated bilinear map of a real-valued quadratic map

Mathlib builds the bilinear map associated with a quadratic map by halving the polar form:
`QuadraticMap.associatedHom` is `⅟(2 : Module.End R N) • QuadraticMap.polarBilin`, with
`QuadraticMap.associated'` the `ℤ`-linear specialisation. Halving needs
`Invertible (2 : Module.End R N)`, and Mathlib's docstring for `associatedHom` names the case
this file supplies:

> Note that this makes the bijection available in more cases than the simpler condition
> `Invertible (2 : R)`, e.g., when `R = ℤ` and `N = ℝ`.

Mathlib does not, however, provide an instance reaching that case: its only route is
`[Invertible (2 : R)] → Invertible (2 : Module.End R M)`, which for `R = ℤ` asks for
`Invertible (2 : ℤ)` and fails. This file closes the gap, so that `associated'` and its API —
`associated_apply`, `associated_isSymm`, `associated_flip`, `associated_eq_self_apply` — become
usable on `ℤ`-quadratic maps with values in a real vector space.

## Main results

* `TauCeti.instInvertibleTwoModuleEndOfModuleReal`: doubling is invertible on any real vector
  space, viewed as an endomorphism of the underlying `ℤ`-module. The scalar ring is fixed to `ℝ`
  rather than left as a variable in which `2` is invertible, because a variable there is not
  determined by the conclusion and so could not be an instance at all.
* `TauCeti.invOf_two_moduleEnd_apply`: the inverse of that doubling acts as the scalar
  `(2 : ℝ)⁻¹`. This is true by `rfl` given the instance, but consumers need it as a rewrite rule:
  it is what turns `associated_apply`'s `⅟(2 : Module.End ℤ N) • ⬝` into ordinary scalar
  arithmetic. It is stated with function application rather than `•`, because `simp` normalises
  a `Module.End` action to application (`Module.End.smul_def`) and the `•` form is therefore not
  in simp-normal form.
-/

public section

namespace TauCeti

variable {N : Type*} [AddCommGroup N] [Module ℝ N]

/-- **Doubling is invertible on a real vector space**, as an endomorphism of its `ℤ`-module
structure. This is the instance Mathlib's `QuadraticMap.associatedHom` needs at `R = ℤ`, `N = ℝ`
and does not have. -/
noncomputable instance instInvertibleTwoModuleEndOfModuleReal :
    Invertible (2 : Module.End ℤ N) where
  invOf := (2 : ℝ)⁻¹ • (1 : Module.End ℤ N)
  -- `ofNat_smul_eq_nsmul` is the bridge: the `2 •` that `Module.End`'s numeral produces is an
  -- `nsmul`, and it has to be matched against the `ℝ`-action before the scalars can cancel.
  invOf_mul_self := by ext x; simp [← ofNat_smul_eq_nsmul ℝ, smul_smul]
  mul_invOf_self := by ext x; simp [← ofNat_smul_eq_nsmul ℝ, smul_smul]

/-- The inverse of doubling acts as the scalar `(2 : ℝ)⁻¹`. -/
@[simp]
theorem invOf_two_moduleEnd_apply (x : N) :
    (⅟(2 : Module.End ℤ N)) x = (2 : ℝ)⁻¹ • x :=
  rfl

end TauCeti
