/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Order.Zorn

/-!
# Maximal abelian subgroups

Every abelian subgroup extends to a maximal one. This existence result is
useful when studying centralizers in CSA groups.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- Every abelian subgroup is contained in a maximal abelian subgroup. -/
theorem exists_le_maximalAbelian (A : Subgroup G) [IsMulCommutative A] :
    ∃ M : Subgroup G, A ≤ M ∧
      Maximal (fun H : Subgroup G => IsMulCommutative H) M := by
  apply zorn_le_nonempty₀ (s := {H : Subgroup G | IsMulCommutative H})
    (x := A) (hxs := inferInstance)
  intro c hc hab y hy
  have : Nonempty c := ⟨⟨y, hy⟩⟩
  have : ∀ i : c, IsMulCommutative (i : Subgroup G) :=
    fun i => hc i.property
  refine ⟨sSup c, ?_, ?_⟩
  · have hcomm := Subgroup.isMulCommutative_iSup
      (S := fun i : c => (i : Subgroup G)) hab.directedOn.directed_val
    simpa [sSup_eq_iSup'] using hcomm
  · intro z hz
    exact le_sSup hz

end Subgroup
