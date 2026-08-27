/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Automorphisms acting on the ring of integers

An automorphism of a number field restricts to the ring of integers, because it preserves
integrality. This file records how that restricted action relates to the ambient one: the
structure map `𝓞 K → K` is equivariant, carrying `σ • z` to `σ` applied to the image of `z`.

Mathlib proves the corresponding statement for a general integral closure
(`integralClosure.coe_smul`), stated with the coercion and with the action written as a scalar
multiplication on both sides. Callers working with a number field invariably want the
`algebraMap` spelling on the left and function application on the right, so that conversion is
made once here rather than at each use site.

## Main results

* `NumberField.algebraMap_smul_eq_apply`: `algebraMap (𝓞 K) K (σ • z) = σ (algebraMap (𝓞 K) K z)`.
-/

public section

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **`algebraMap` intertwines the Galois actions on `𝓞 K` and on `K`.** The action on the ring
of integers is the restriction of the action on `K` (`integralClosure.coe_smul`), so the structure
map sends `σ • z` to `σ` applied to the image of `z`.

Not named `algebraMap_smul`: that is Mathlib's unrelated `algebraMap R A r • m = r • m`. -/
@[simp] theorem algebraMap_smul_eq_apply (σ : K ≃ₐ[ℚ] K) (z : 𝓞 K) :
    algebraMap (𝓞 K) K (σ • z) = σ (algebraMap (𝓞 K) K z) := by
  have hcoe : algebraMap (𝓞 K) K (σ • z) = σ • algebraMap (𝓞 K) K z := by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact integralClosure.coe_smul σ z
  rw [hcoe, AlgEquiv.smul_def]

end NumberField
