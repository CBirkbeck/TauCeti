/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Generated
import TauCeti.Algebra.Lie.Basic

/-!
# The first three standard sl₂ modules

The actions of `V(0)` and `V(1)` are respectively zero and ordinary matrix multiplication.
For `V(2)`, the actual raising matrix is a primitive vector of adjoint weight two; its generated
Lie submodule has dimension three and is the whole matrix Lie algebra. The resulting equivalence
is a Lie-module equivalence, rather than only a dimension or character comparison.

-/

public section

open LieAlgebra LieModule

namespace TauCeti.Sl2Std

section Adjoint

variable (K : Type*) [Field K] [CharZero K]

/-- The adjoint representation of actual matrix `sl₂` is isomorphic to `V(2)`. -/
theorem nonempty_lieModuleEquiv_adjoint :
    Nonempty (SpecialLinear.sl (Fin 2) K ≃ₗ⁅K, SpecialLinear.sl (Fin 2) K⁆ Sl2Std K 2) := by
  have hP : (isSl2Triple_single (R := K) (zero_ne_one : (0 : Fin 2) ≠ 1)).HasPrimitiveVectorWith
      (slFinTwoBasis K 0) (2 : K) := by
    refine ⟨(slFinTwoBasis K).ne_zero 0, ?_, ?_⟩
    · simpa only [slFinTwoBasis_two] using lie_slFinTwoBasis_two_zero K
    · simp only [← slFinTwoBasis_zero, lie_self]
  let p := LieSubmodule.lieSpan K (SpecialLinear.sl (Fin 2) K) {slFinTwoBasis K 0}
  obtain ⟨e⟩ := Sl2Std.nonempty_lieModuleEquiv_lieSpan_singleton (n := 2) hP
  have hd : Module.finrank K p = Module.finrank K (SpecialLinear.sl (Fin 2) K) := by
    rw [e.toLinearEquiv.finrank_eq, Sl2Std.finrank_eq,
      Module.finrank_eq_card_basis (slFinTwoBasis K)]
    simp only [Fintype.card_fin]
  have ht : p.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq hd
  have hp : Function.Bijective p.incl := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    change x ∈ p.toSubmodule
    rw [ht]
    trivial
  exact ⟨(TauCeti.LieModuleEquiv.ofBijective p.incl hp).symm.trans e⟩


end Adjoint

variable (K : Type*) [CommRing K]

/-- Every Lie algebra element acts as zero on the one-dimensional module `V(0)`. -/
theorem lie_eq_zero (x : SpecialLinear.sl (Fin 2) K) (v : Sl2Std K 0) : ⁅x, v⁆ = 0 := by
  rw [eq_smul_single_add_smul_single_add_smul_singleSubSingle x zero_ne_one]
  simp only [add_lie, smul_lie, ← slFinTwoBasis_zero, ← slFinTwoBasis_one,
    ← slFinTwoBasis_two, Sl2Std.lie_slFinTwoBasis_zero, Sl2Std.lie_slFinTwoBasis_one,
    Sl2Std.lie_slFinTwoBasis_two]
  apply funext
  intro i
  fin_cases i
  simp [Sl2Std.diag_apply]

/-- The action on `V(1)` is ordinary multiplication by the underlying two-by-two matrix. -/
theorem lie_eq_mulVec (x : SpecialLinear.sl (Fin 2) K) (v : Sl2Std K 1) :
    (fun i : Fin 2 => (⁅x, v⁆ : Sl2Std K 1) i) = x.val.mulVec v := by
  rw [eq_smul_single_add_smul_single_add_smul_singleSubSingle x zero_ne_one]
  simp only [add_lie, smul_lie, ← slFinTwoBasis_zero, ← slFinTwoBasis_one,
    ← slFinTwoBasis_two, Sl2Std.lie_slFinTwoBasis_zero, Sl2Std.lie_slFinTwoBasis_one,
    Sl2Std.lie_slFinTwoBasis_two]
  ext i
  fin_cases i <;>
    simp [Sl2Std.raise_apply, Sl2Std.lower_apply, Sl2Std.diag_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

end TauCeti.Sl2Std
