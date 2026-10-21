/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg
public import TauCeti.GroupTheory.ProperPower

/-!
# Proper powers in free groups

Free generators and commutators of distinct generators are not proper powers. The latter
is detected by the integer Heisenberg group: the commutator has central coordinate one.
-/

public section

private theorem not_dvd_one_of_two_le (n : ℕ) (hn : 2 ≤ n) (hdiv : (n : ℤ) ∣ 1) : False := by
  have hdiv' : n ∣ 1 := Int.natCast_dvd_natCast.mp hdiv
  have hle : n ≤ 1 := Nat.le_of_dvd (by omega) hdiv'
  omega

private theorem not_isProperPower_ofAdd_one :
    ¬ Group.IsProperPower (Multiplicative.ofAdd (1 : ℤ)) := by
  intro h
  obtain ⟨y, n, hn, heq⟩ := Group.isProperPower_iff.mp h
  have hdiv : (n : ℤ) ∣ 1 := by
    refine ⟨y.toAdd, ?_⟩
    simpa using congrArg Multiplicative.toAdd heq
  exact not_dvd_one_of_two_le n hn hdiv

private theorem not_isProperPower_heisenberg_zOne :
    ¬ Group.IsProperPower (⟨0, 0, 1⟩ : TauCeti.HeisenbergGroup ℤ) := by
  intro h
  obtain ⟨y, n, hn, heq⟩ := Group.isProperPower_iff.mp h
  have hx := congrArg TauCeti.HeisenbergGroup.x heq
  have hy := congrArg TauCeti.HeisenbergGroup.y heq
  simp only [TauCeti.HeisenbergGroup.pow_eq, Int.nsmul_eq_mul, zero_eq_mul,
    Int.natCast_eq_zero] at hx hy
  have hxy : y.x = 0 ∧ y.y = 0 := by
    constructor <;> omega
  have hz := congrArg TauCeti.HeisenbergGroup.z heq
  simp only [TauCeti.HeisenbergGroup.pow_eq, hxy.1, nsmul_zero, hxy.2,
    Int.nsmul_eq_mul, mul_zero, add_zero] at hz
  exact not_dvd_one_of_two_le n hn ⟨y.z, hz⟩

namespace FreeGroup

variable {α : Type*}
open scoped commutatorElement

/-- The square of any free generator is a proper power. -/
theorem isProperPower_of_sq (a : α) : Group.IsProperPower (of a ^ 2) :=
  Group.isProperPower_pow (of a) (by omega)

/-- A free generator is not a proper power. -/
@[simp] theorem not_isProperPower_of (a : α) : ¬ Group.IsProperPower (of a) := by
  classical
  let f : FreeGroup α →* Multiplicative ℤ :=
    FreeGroup.lift (fun b => if b = a then Multiplicative.ofAdd 1 else 1)
  intro h
  exact not_isProperPower_ofAdd_one (by simpa [f] using Group.IsProperPower.map f h)

/-- The commutator of two distinct free generators is not a proper power. -/
theorem not_isProperPower_commutator {a b : α} (hab : a ≠ b) :
    ¬ Group.IsProperPower ⁅of a, of b⁆ := by
  classical
  let f : FreeGroup α →* TauCeti.HeisenbergGroup ℤ :=
    FreeGroup.lift (fun c =>
      if c = a then ⟨1, 0, 0⟩ else if c = b then ⟨0, 1, 0⟩ else 1)
  have ha : f (of a) = ⟨1, 0, 0⟩ := by simp [f]
  have hb : f (of b) = ⟨0, 1, 0⟩ := by simp [f, hab.symm]
  intro h
  apply not_isProperPower_heisenberg_zOne
  simpa [ha, hb, TauCeti.HeisenbergGroup.commutatorElement_eq] using
    Group.IsProperPower.map f h

end FreeGroup
