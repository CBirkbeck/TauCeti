/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Basic

/-!
# Proper powers in groups

A proper power is a power with a natural exponent at least two. In particular the identity is
a proper power; the predicate makes no exception for it. Homomorphisms preserve proper powers.
-/

public section

namespace Group

/-- An element of a group is a proper power if it has a root with exponent at least two. -/
def IsProperPower {G : Type*} [Group G] (x : G) : Prop :=
  ∃ (y : G) (n : ℕ), 2 ≤ n ∧ x = y ^ n

/-- The root-and-exponent characterization of a proper power. -/
theorem isProperPower_iff {G : Type*} [Group G] {x : G} :
    IsProperPower x ↔ ∃ (y : G) (n : ℕ), 2 ≤ n ∧ x = y ^ n :=
  Iff.rfl

namespace IsProperPower

/-- Homomorphisms preserve proper powers. -/
theorem map {G H : Type*} [Group G] [Group H] (f : G →* H) {x : G}
    (hx : IsProperPower x) : IsProperPower (f x) := by
  obtain ⟨y, n, hn, rfl⟩ := hx
  exact ⟨f y, n, hn, by simp⟩

/-- The identity is a proper power in every group. -/
@[simp] theorem one {G : Type*} [Group G] : IsProperPower (1 : G) :=
  ⟨1, 2, Nat.le_refl 2, by simp⟩

end IsProperPower

/-- Every natural power with exponent at least two is a proper power. -/
theorem isProperPower_pow {G : Type*} [Group G] (y : G) {n : ℕ} (hn : 2 ≤ n) :
    IsProperPower (y ^ n) :=
  ⟨y, n, hn, rfl⟩

/-- An integer power with absolute exponent at least two is a proper power. -/
theorem isProperPower_zpow {G : Type*} [Group G] (y : G) {n : ℤ}
    (hn : 2 ≤ n.natAbs) : IsProperPower (y ^ n) := by
  rcases Int.natAbs_eq n with h | h
  · rw [h, zpow_natCast]
    exact isProperPower_pow y hn
  · rw [h, zpow_neg, zpow_natCast]
    simpa only [inv_pow] using isProperPower_pow y⁻¹ hn

end Group
