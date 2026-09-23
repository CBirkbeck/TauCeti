/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Integral

/-!
# The ray class count, reindexed by a representative ideal

Counting the integral ideals of a fixed ray class is awkward directly, because the class
condition is not a divisibility condition.  Multiplying by an ideal `𝔞` whose class is the
inverse one turns it into two conditions that are: divisibility by `𝔞`, and triviality of the
class.  The norm bound is carried along, scaled by the norm of `𝔞`.

## Main definitions

* `TauCeti.GlobalNumberFields.mulDvdEquiv`: multiplying by `𝔞` is a bijection onto the multiples
  of `𝔞`.
* `TauCeti.GlobalNumberFields.countReindexEquiv`: the reindexing described above.

## Main results

* `TauCeti.GlobalNumberFields.mul_right_injective_integralIdealsPrimeTo`: multiplication by a
  fixed member of the prime-to monoid is injective.
* `TauCeti.GlobalNumberFields.mulDvdEquiv_apply_coe`: the ideal underlying `mulDvdEquiv I` is
  `𝔞 * I`, so a consumer never has to unfold the equivalence.
* `TauCeti.GlobalNumberFields.rayClassIdealCountingFunction_eq_card_dvd_and_idealClass_eq_one`:
  the counting function as the number of multiples of `𝔞` of trivial class and bounded norm.
-/

public section

open NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- Multiplication by a fixed member of the prime-to monoid is injective. -/
theorem mul_right_injective_integralIdealsPrimeTo (𝔪 : Modulus K) (𝔞 : integralIdealsPrimeTo 𝔪) :
    Function.Injective (fun I : integralIdealsPrimeTo 𝔪 ↦ 𝔞 * I) := fun _ _ h ↦
  -- the members are nonzero, and nonzero ideals of a Dedekind domain cancel
  Subtype.ext (mul_left_cancel₀ (ne_bot_of_mem_integralIdealsPrimeTo 𝔞.prop)
    (congrArg Subtype.val h))

-- `Equiv.dvd` is this bijection for a `LeftCancelSemigroup`, an instance that
-- `integralIdealsPrimeTo 𝔪` does not carry.
/-- Multiplying by `𝔞` is a bijection onto the multiples of `𝔞`. -/
noncomputable def mulDvdEquiv (𝔪 : Modulus K) (𝔞 : integralIdealsPrimeTo 𝔪) :
    integralIdealsPrimeTo 𝔪 ≃ {I : integralIdealsPrimeTo 𝔪 // 𝔞 ∣ I} :=
  Equiv.ofBijective (fun I ↦ ⟨𝔞 * I, I, rfl⟩)
    ⟨fun _ _ h ↦ mul_right_injective_integralIdealsPrimeTo 𝔪 𝔞 (congrArg Subtype.val h),
      fun I ↦ I.prop.imp fun _ hI ↦ Subtype.ext hI.symm⟩

-- `mulDvdEquiv` is not `@[expose]`d, so the parentheses in `(rfl)` keep the definitional step
-- inside this module, leaving this lemma as the interface for importers.
@[simp]
theorem mulDvdEquiv_apply_coe (𝔪 : Modulus K) (𝔞 I : integralIdealsPrimeTo 𝔪) :
    (mulDvdEquiv 𝔪 𝔞 I : integralIdealsPrimeTo 𝔪) = 𝔞 * I := (rfl)

/-- **The ray class count, reindexed by a representative.**  For `𝔞` in the inverse class of `c`,
multiplication by `𝔞` matches the ideals of class `c` with norm at most `x` against the multiples
of `𝔞` of trivial class with norm at most `x * N 𝔞`. -/
noncomputable def countReindexEquiv (𝔪 : Modulus K) {c : RayClassGroup 𝔪}
    (𝔞 : integralIdealsPrimeTo 𝔪) (h𝔞 : idealClass 𝔪 𝔞 = c⁻¹) (x : ℝ) :
    {I : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 I = c ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} ≃
      {I : integralIdealsPrimeTo 𝔪 // 𝔞 ∣ I ∧ idealClass 𝔪 I = 1 ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x * Ideal.absNorm (𝔞 : Ideal (𝓞 K))} :=
  ((mulDvdEquiv 𝔪 𝔞).subtypeEquiv fun I ↦ by
    simp only [mulDvdEquiv_apply_coe, Submonoid.coe_mul, map_mul, h𝔞, Nat.cast_mul,
      inv_mul_eq_one, mul_comm x]
    -- `N 𝔞` is nonzero, so it cancels from the scaled norm bound
    exact and_congr eq_comm (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (mt Ideal.absNorm_eq_zero_iff.mp (ne_bot_of_mem_integralIdealsPrimeTo 𝔞.prop))))).symm).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : integralIdealsPrimeTo 𝔪 ↦ 𝔞 ∣ I) _)

/-- **The counting function as a count of multiples of `𝔞`.**  For `𝔞` in the inverse class of
`c`, the count runs over the multiples of `𝔞` of trivial class, against a norm bound scaled by
`N 𝔞`; any `𝔞` of that class serves, as the left-hand side does not mention it.  This is the
rewrite that trades the class condition for a divisibility condition, where
`rayClassIdealCountingFunction_def` is the one that keeps the class condition. -/
theorem rayClassIdealCountingFunction_eq_card_dvd_and_idealClass_eq_one (𝔪 : Modulus K)
    {c : RayClassGroup 𝔪} (𝔞 : integralIdealsPrimeTo 𝔪) (h𝔞 : idealClass 𝔪 𝔞 = c⁻¹) (x : ℝ) :
    rayClassIdealCountingFunction 𝔪 c x = Nat.card {I : integralIdealsPrimeTo 𝔪 // 𝔞 ∣ I ∧
      idealClass 𝔪 I = 1 ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤
        x * Ideal.absNorm (𝔞 : Ideal (𝓞 K))} :=
  -- `rayClassIdealCountingFunction` is not `@[expose]`d, so the step onto the cardinality it is
  -- defined as goes through `rayClassIdealCountingFunction_def` rather than by `rfl`
  (rayClassIdealCountingFunction_def 𝔪 c x).trans <| Nat.card_congr <| countReindexEquiv 𝔪 𝔞 h𝔞 x

end TauCeti.GlobalNumberFields
