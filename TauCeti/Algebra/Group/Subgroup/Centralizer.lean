/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Subgroup.centralizer` occurs in the statement below.
public import Mathlib.GroupTheory.Subgroup.Centralizer
-- `Commute.units_val_iff` transports commutation between units and their values.
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.Torsion
import Mathlib.Tactic.Group

/-!
# Centralizers and maximal commutative subgroups

Centralizers of a group of units are computed on the underlying monoid: a unit centralizes another
exactly when their values commute. Mathlib has both halves —
`Subgroup.mem_centralizer_singleton_iff` turns membership into an equation, and
`Commute.units_val_iff` transports that equation between `Mˣ` and `M` — but not their combination,
which is the form every concrete centralizer computation in a matrix group starts from.

## Main results

* `TauCeti.mem_centralizer_singleton_iff_commute_val`: a unit lies in the centralizer of a unit `g`
  exactly when the two commute as elements of the monoid.
* `Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative`: a self-centralizing subgroup is
  maximal among commutative subgroups.
* `Commute.zpow_left_iff` and `Commute.pow_left_iff`: commuting with a nonzero power is equivalent
  to commuting with its base in groups with unique roots.
* `Subgroup.centralizer_zpow_eq` and `Subgroup.centralizer_pow_eq`: nonzero powers have the same
  centralizer as their base in groups with unique roots.
-/

public section

namespace TauCeti

/-- Membership in the centralizer of a unit `g`, read on the underlying monoid. -/
theorem mem_centralizer_singleton_iff_commute_val {M : Type*} [Monoid M] {g h : Mˣ} :
    h ∈ Subgroup.centralizer {g} ↔ Commute (g : M) (h : M) :=
  ⟨fun hh => Commute.units_val_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hh).symm,
    fun hh => Subgroup.mem_centralizer_singleton_iff.mpr (Commute.units_val_iff.mp hh).symm⟩

end TauCeti

namespace Subgroup

/-- A self-centralizing subgroup is maximal among commutative subgroups. -/
theorem eq_of_centralizer_eq_self_of_le_of_isMulCommutative {G : Type*} [Group G]
    {S H : Subgroup G} (hS : Subgroup.centralizer (S : Set G) = S) [IsMulCommutative H]
    (hle : S ≤ H) :
    H = S :=
  le_antisymm
    (by
      rw [← hS]
      exact (Subgroup.le_centralizer (H := H)).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)))
    hle

end Subgroup

namespace Commute

variable {G : Type*} [Group G] [HasUniqueRoots G] {x y : G}

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_left_iff {n : ℤ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  constructor
  · intro h
    have hconj : y⁻¹ * x * y = x := by
      apply zpow_left_injective hn
      calc
        (y⁻¹ * x * y) ^ n = y⁻¹ * x ^ n * y := by
          simpa only [inv_inv] using (conj_zpow (a := y⁻¹) (b := x) (i := n))
        _ = x ^ n := h.symm.inv_mul_cancel
    exact calc
      x * y = y * (y⁻¹ * x * y) := by group
      _ = y * x := by rw [hconj]
  · intro h
    exact h.zpow_left n

/-- In a group with unique roots, an element commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_left_iff {n : ℕ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using (zpow_left_iff (x := x) (y := y) hn')

end Commute

namespace Subgroup

variable {G : Type*} [Group G] [HasUniqueRoots G] (x : G)

/-- Taking a nonzero integer power does not change the centralizer of an element in a group
with unique roots. -/
@[simp]
theorem centralizer_zpow_eq {n : ℤ} (hn : n ≠ 0) :
    centralizer {x ^ n} = centralizer {x} := by
  ext y
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    ← commute_iff_eq, ← commute_iff_eq, Commute.symm_iff,
    Commute.zpow_left_iff hn, Commute.symm_iff]

/-- Taking a nonzero natural power does not change the centralizer of an element in a group
with unique roots. -/
@[simp]
theorem centralizer_pow_eq {n : ℕ} (hn : n ≠ 0) :
    centralizer {x ^ n} = centralizer {x} := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using centralizer_zpow_eq x hn'

end Subgroup
