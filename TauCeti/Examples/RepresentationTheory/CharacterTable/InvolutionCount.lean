/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.InvolutionCount
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Basic.Complex.Basic

/-!
# Frobenius–Schur counts for the quaternion and dihedral groups of order eight

Finite enumeration independently counts the square roots of the identity in `Q₈` and `D₄`.
The character-table formula then verifies that the degree-weighted indicator sums are two and
six respectively. The identity is included in each count.


-/

public section

namespace TauCeti.Examples.FrobeniusSchur

/-- The quaternion square-root count and degree-weighted indicator sum are both two. -/
example : Nat.card {g : QuaternionGroup 2 // g * g = 1} = 2 ∧
    (∑ i : Fin (Nat.card (ConjClasses (QuaternionGroup 2))),
      frobeniusSchurIndicatorRow ℂ i * (characterDegree ℂ i : ℂ)) = 2 := by
  have hc : Nat.card {g : QuaternionGroup 2 // g * g = 1} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  refine ⟨hc, ?_⟩
  rw [← card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree]
  simp only [hc, Nat.cast_ofNat]

/-- The dihedral square-root count and degree-weighted indicator sum are both six. -/
example : Nat.card {g : DihedralGroup 4 // g * g = 1} = 6 ∧
    (∑ i : Fin (Nat.card (ConjClasses (DihedralGroup 4))),
      frobeniusSchurIndicatorRow ℂ i * (characterDegree ℂ i : ℂ)) = 6 := by
  have hc : Nat.card {g : DihedralGroup 4 // g * g = 1} = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  refine ⟨hc, ?_⟩
  rw [← card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree]
  simp only [hc, Nat.cast_ofNat]

end TauCeti.Examples.FrobeniusSchur
