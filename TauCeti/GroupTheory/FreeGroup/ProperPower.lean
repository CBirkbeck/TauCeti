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

namespace FreeGroup

variable {α : Type*}
open scoped commutatorElement

/-- The square of any free generator is a proper power. -/
theorem isProperPower_of_sq (a : α) : Group.IsProperPower (of a ^ 2) :=
  Group.isProperPower_pow (of a) (by omega)

/-- A free generator is not a proper power. -/
@[simp] theorem not_isProperPower_of (a : α) : ¬ Group.IsProperPower (of a) := by
  classical
  intro ha
  obtain ⟨y, n, hn, hy⟩ := Group.isProperPower_iff.mp ha
  let f : FreeGroup α →* Multiplicative ℤ :=
    FreeGroup.lift (fun b => if b = a then Multiplicative.ofAdd 1 else 1)
  have hf : f (of a) = Multiplicative.ofAdd 1 := by simp [f]
  have hpow : Multiplicative.ofAdd (1 : ℤ) = (f y) ^ n := by
    simpa [hf] using congrArg f hy
  have hdiv : n ∣ (1 : ℕ) := by
    apply Int.natCast_dvd_natCast.mp
    refine ⟨(f y).toAdd, ?_⟩
    simpa using congrArg Multiplicative.toAdd hpow
  have hle : n ≤ 1 := Nat.le_of_dvd (by omega) hdiv
  omega

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
  obtain ⟨y, n, hn, heq⟩ := Group.isProperPower_iff.mp (Group.IsProperPower.map f h)
  have hz : (⟨0, 0, 1⟩ : TauCeti.HeisenbergGroup ℤ) = y ^ n := by
    simpa [ha, hb, TauCeti.HeisenbergGroup.commutatorElement_eq] using heq
  have hx : y.x = 0 := by
    have hxy := congrArg TauCeti.HeisenbergGroup.x hz
    simp only [TauCeti.HeisenbergGroup.pow_eq, Int.nsmul_eq_mul, zero_eq_mul,
      Int.natCast_eq_zero] at hxy
    rcases hxy with hn0 | hy0
    · omega
    · exact hy0
  have hy : y.y = 0 := by
    have hyy := congrArg TauCeti.HeisenbergGroup.y hz
    simp only [TauCeti.HeisenbergGroup.pow_eq, Int.nsmul_eq_mul, zero_eq_mul,
      Int.natCast_eq_zero] at hyy
    rcases hyy with hn0 | hy0
    · omega
    · exact hy0
  have hz' := congrArg TauCeti.HeisenbergGroup.z hz
  simp only [TauCeti.HeisenbergGroup.pow_eq, hx, nsmul_zero, hy, Int.nsmul_eq_mul,
    mul_zero, add_zero] at hz'
  have hdiv : n ∣ (1 : ℕ) := by
    apply Int.natCast_dvd_natCast.mp
    exact ⟨y.z, hz'⟩
  have hle : n ≤ 1 := Nat.le_of_dvd (by omega) hdiv
  omega

end FreeGroup
