/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Generated

/-!
# The adjoint standard sl₂ module

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
  obtain ⟨e⟩ : Nonempty (p ≃ₗ⁅K, SpecialLinear.sl (Fin 2) K⁆ Sl2Std K 2) :=
    Sl2Std.nonempty_lieModuleEquiv_lieSpan_singleton (n := 2) hP
  have hd : Module.finrank K p = Module.finrank K (SpecialLinear.sl (Fin 2) K) := by
    rw [e.toLinearEquiv.finrank_eq, Sl2Std.finrank_eq,
      Module.finrank_eq_card_basis (slFinTwoBasis K)]
    simp only [Fintype.card_fin]
  have ht : p = ⊤ :=
    (LieSubmodule.toSubmodule_eq_top p).mp (Submodule.eq_top_of_finrank_eq hd)
  rw [ht] at e
  exact ⟨(LieModuleEquiv.ofTop K (SpecialLinear.sl (Fin 2) K) _).symm.trans e⟩

end Adjoint

end TauCeti.Sl2Std
