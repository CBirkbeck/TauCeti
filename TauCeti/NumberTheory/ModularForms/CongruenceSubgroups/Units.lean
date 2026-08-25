/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The diamond label of `Γ₀(N)` under reduction of the level

`CongruenceSubgroup.Gamma0Map` reads off the lower-right entry of a matrix of `Γ₀(N)` in
`ZMod N`, and `Gamma0Map_toHomUnits` is its unit-valued form. This file records the one fact
about that label which needs the reduction map `ZMod.unitsMap`: for `M ∣ N`, reading a matrix
of `Γ₀(N)` as a matrix of `Γ₀(M)` reduces its label along `(ZMod N)ˣ → (ZMod M)ˣ`.

It sits beside `TauCeti.NumberTheory.ModularForms.CongruenceSubgroups` rather than inside it
because the statement is the only thing in the congruence-subgroup API that mentions
`ZMod.unitsMap`. Putting it here keeps that foundational module from re-exporting
`Mathlib.Data.ZMod.Units` to its whole downstream cone.

## Main results

* `CongruenceSubgroup.Gamma0Map_toHomUnits_of_dvd`: for `M ∣ N`, the diamond label of a
  `Γ₀(N)` matrix read in `Γ₀(M)` is the reduction of its label at level `N`.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CongruenceSubgroup

/-- **The diamond label is compatible with reduction.** For `M ∣ N`, a matrix of `Γ₀(N)` read as
a matrix of `Γ₀(M)` has lower-right entry the reduction of its lower-right entry at level `N`,
so a nebentypus character pulls back along `(ZMod N)ˣ → (ZMod M)ˣ`. -/
@[simp]
lemma Gamma0Map_toHomUnits_of_dvd {M N : ℕ} (h : M ∣ N) (γ : ↥(Gamma0 N)) :
    (Gamma0Map M).toHomUnits ⟨(γ : SL(2, ℤ)), Gamma0_le_Gamma0_of_dvd h γ.2⟩ =
      ZMod.unitsMap h ((Gamma0Map N).toHomUnits γ) := by
  ext
  simp [Gamma0Map, ZMod.unitsMap_def]

end CongruenceSubgroup
