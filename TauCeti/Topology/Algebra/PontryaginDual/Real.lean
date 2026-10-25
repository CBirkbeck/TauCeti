/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Topology.Algebra.PontryaginDual

/-!
# Real exponential characters

A real frequency `t` gives the continuous character `x ↦ exp(i t x)` of the additive real
line. This parametrization is continuous for the compact-open topology on the Pontryagin dual.
-/

public section

namespace Real

/-- The character of the additive real line with frequency `t`, in the `exp(i t x)` convention. -/
noncomputable def pontryaginCharacter (t : ℝ) : PontryaginDual (Multiplicative ℝ) where
  toFun x := Circle.exp (t * x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp [mul_add, Circle.exp_add]
  continuous_toFun := by fun_prop

/-- The character at frequency `t` evaluates to `exp(i t x)`. -/
@[simp] theorem pontryaginCharacter_apply (t : ℝ) (x : Multiplicative ℝ) :
    pontryaginCharacter t x = Circle.exp (t * x.toAdd) := by
  rfl

/-- The exponential character depends continuously on its real frequency. -/
@[fun_prop] theorem continuous_pontryaginCharacter : Continuous pontryaginCharacter :=
  ContinuousMonoidHom.continuous_of_continuous_uncurry _ (by
    change Continuous fun p : ℝ × Multiplicative ℝ => Circle.exp (p.1 * p.2.toAdd)
    fun_prop)

end Real
