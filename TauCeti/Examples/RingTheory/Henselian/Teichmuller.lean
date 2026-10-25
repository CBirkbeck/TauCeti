/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Teichmuller
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.Henselian
public import Mathlib.Algebra.Field.ZMod

/-!
# Teichmüller values for Q₂ and Q₅

These are the worked Teichmüller values requested by
TauCetiRoadmap/LocalFieldsRamification/README.md,
Layer 1. The Q₂ section is constant 1. For Q₅ the residues 1 and 4 lift to 1 and −1, respectively;
the lift of 2 is the square root of −1 reducing to 2, and the lift of 3 is its negative.
The computations use the native valuative integer ring and its proved residue-field comparison.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti.Examples.Teichmuller

local instance prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Every nonzero residue over Q₂ has Teichmüller lift 1. -/
theorem padic_two (x : (𝓀[ℚ_[2]])ˣ) : TauCeti.teichmuller 𝒪[ℚ_[2]] x = 1 := by
  have h := TauCeti.teichmuller_pow_card_sub_one 𝒪[ℚ_[2]] x
  simpa only [Padic.natCard_residueField, Nat.reduceSub, pow_one] using h

/-- Over Q₅, the residue −1 has Teichmüller lift −1. -/
theorem padic_five_neg_one : TauCeti.teichmuller 𝒪[ℚ_[5]] (-1) = -1 := by
  apply TauCeti.teichmuller_neg_one
  rw [Padic.natCard_residueField]
  decide

/-- The native residue field of Q₅ identified with ZMod 5. -/
noncomputable def residueEquivZModFive : 𝓀[ℚ_[5]] ≃+* ZMod 5 :=
  (ResidueField.mapEquiv (Padic.integerRingEquiv 5)).trans PadicInt.residueField

/-- The residue unit 2 in the native residue field of Q₅. -/
noncomputable def residueTwo : (𝓀[ℚ_[5]])ˣ :=
  (Units.mapEquiv residueEquivZModFive.toMulEquiv).symm (Units.mk0 (2 : ZMod 5) (by decide))

/-- The residue unit 2 over Q₅ squares to −1. -/
theorem residue_two_sq : residueTwo ^ 2 = -1 := by
  apply (Units.mapEquiv residueEquivZModFive.toMulEquiv).injective
  ext
  simp only [RingEquiv.toMulEquiv_eq_coe, residueTwo, Units.mapEquiv_symm, map_pow,
    Units.val_pow_eq_pow_val, Units.coe_mapEquiv, Units.val_mk0,
    RingEquiv.coe_coe_toMulEquiv_symm, RingEquiv.coe_toMulEquiv,
    RingEquiv.apply_symm_apply, Units.val_neg, Units.val_one, RingEquiv.map_neg_one]
  decide

/-- The Teichmüller lift of the residue 2 over Q₅ is a square root of −1. -/
theorem padic_five_two_sq : TauCeti.teichmuller 𝒪[ℚ_[5]] residueTwo ^ 2 = -1 := by
  rw [← map_pow, residue_two_sq, padic_five_neg_one]

/-- The chosen square root of −1 reduces to 2, fixing its sign. -/
theorem padic_five_two_residue :
    residueEquivZModFive
      (residue 𝒪[ℚ_[5]] (TauCeti.teichmuller 𝒪[ℚ_[5]] residueTwo : 𝒪[ℚ_[5]])) = 2 := by
  simp only [residueTwo, RingEquiv.toMulEquiv_eq_coe, Units.mapEquiv_symm,
    residue_teichmuller, Units.coe_mapEquiv, Units.val_mk0,
    RingEquiv.coe_coe_toMulEquiv_symm, RingEquiv.apply_symm_apply]

/-- The residue 1 over Q₅ has Teichmüller lift 1. -/
theorem padic_five_one : TauCeti.teichmuller 𝒪[ℚ_[5]] (1 : (𝓀[ℚ_[5]])ˣ) = 1 := map_one _

/-- The negative of the residue unit 2 is the residue 3. -/
theorem padic_five_three_residue : residueEquivZModFive (-residueTwo : 𝓀[ℚ_[5]]) = 3 := by
  simp only [residueTwo, RingEquiv.toMulEquiv_eq_coe, Units.mapEquiv_symm,
    Units.coe_mapEquiv, Units.val_mk0, RingEquiv.coe_coe_toMulEquiv_symm,
    map_neg, RingEquiv.apply_symm_apply]
  decide

/-- The Teichmüller lift of 3 is the negative of the Teichmüller lift of 2. -/
theorem padic_five_three : TauCeti.teichmuller 𝒪[ℚ_[5]] (-residueTwo) =
    -TauCeti.teichmuller 𝒪[ℚ_[5]] residueTwo := by
  rw [show -residueTwo = (-1) * residueTwo from by simp, map_mul]
  rw [TauCeti.teichmuller_neg_one _ (by rw [Padic.natCard_residueField]; decide)]
  simp

end TauCeti.Examples.Teichmuller
