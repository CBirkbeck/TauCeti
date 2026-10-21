/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Centralizers of powers in groups with unique roots

In a group with unique roots, commuting with a nonzero power of an element is equivalent to
commuting with the element itself. Hence taking a nonzero power does not change its centralizer.
For free groups this allows centralizer calculations to pass between an element and each of its
nontrivial roots, including maximal roots.
-/

public section

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
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro hy
    exact ((Commute.zpow_left_iff (x := x) (y := y) hn).mp hy.symm).symm
  · intro hy
    exact ((Commute.zpow_left_iff (x := x) (y := y) hn).mpr hy.symm).symm

/-- Taking a nonzero natural power does not change the centralizer of an element in a group
with unique roots. -/
@[simp]
theorem centralizer_pow_eq {n : ℕ} (hn : n ≠ 0) :
    centralizer {x ^ n} = centralizer {x} := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using centralizer_zpow_eq x hn'

end Subgroup
