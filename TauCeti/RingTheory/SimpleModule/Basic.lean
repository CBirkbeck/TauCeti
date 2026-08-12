/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Binary products of semisimple modules

Mathlib closes `IsSemisimpleModule` under submodules, quotients, `Finsupp`, and finite dependent
products `Π i, M i`. The dependent product covers a binary product only when both factors lie in
the same universe, since the family `M : ι → Type u` is universe-monomorphic; this file supplies
the binary case with the two factors in unrelated universes.

## Main results

* `TauCeti.IsSemisimpleModule.prod`: a product of two semisimple modules is semisimple.
-/

public section

namespace TauCeti

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **A product of two semisimple modules is semisimple.** -/
theorem IsSemisimpleModule.prod [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) := by
  -- `M × N` is the join of the two coordinate copies, each of which is a semisimple submodule.
  have hM : IsSemisimpleModule R (LinearMap.range (LinearMap.inl R M N)) :=
    .congr (LinearEquiv.ofInjective _ LinearMap.inl_injective).symm
  have hN : IsSemisimpleModule R (LinearMap.range (LinearMap.inr R M N)) :=
    .congr (LinearEquiv.ofInjective _ LinearMap.inr_injective).symm
  have hsup := _root_.IsSemisimpleModule.sup hM hN
  rw [LinearMap.sup_range_inl_inr] at hsup
  exact .congr Submodule.topEquiv.symm

end TauCeti
