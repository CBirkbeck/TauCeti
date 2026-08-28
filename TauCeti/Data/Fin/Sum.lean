/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# The two-element sum as `Fin 2`

`Unit ⊕ Unit` and `Fin 2` are the two ways a two-element index type arises: one variable per
named slot, or one variable per numeral. Translating between them is pure bookkeeping, needed
wherever an object indexed by named slots must be presented against an API indexed by `Fin 2`.

Mathlib has `boolEquivPUnitSumPUnit` and `finSumFinEquiv`, but nothing of this shape; composing
those two routes through `Bool` and a `PUnit` universe adjustment for no gain.

## Main definitions

* `unitSumUnitEquivFinTwo`: the equivalence `Unit ⊕ Unit ≃ Fin 2`, sending the left summand to
  `0` and the right to `1`.
-/

public section

/-- The equivalence `Unit ⊕ Unit ≃ Fin 2`, sending the left summand to `0` and the right to `1`.

An `Equiv` rather than a bare `Function.Embedding`: injectivity is what turns a coefficient under
a reindexing into an equality rather than a sum over a fibre, but surjectivity is what lets a
statement about *every* `Fin 2` index be pulled back, and both directions are wanted downstream. -/
def unitSumUnitEquivFinTwo : (Unit ⊕ Unit) ≃ Fin 2 where
  toFun := Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)
  invFun := ![Sum.inl (), Sum.inr ()]
  left_inv := by rintro (⟨⟩ | ⟨⟩) <;> rfl
  right_inv := by intro x; fin_cases x <;> rfl

@[simp]
theorem unitSumUnitEquivFinTwo_inl : unitSumUnitEquivFinTwo (Sum.inl ()) = 0 := by decide

@[simp]
theorem unitSumUnitEquivFinTwo_inr : unitSumUnitEquivFinTwo (Sum.inr ()) = 1 := by decide
