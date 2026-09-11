/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion

/-!
# Upper-triangular slashes of a level-raise

For `g` slash-invariant of level `Γ₁(M)`, the level-raise `V_p g = p^(1-k) • (g ∣[k] scaleGL p)`
(the function `τ ↦ g (p τ)`) is slashed by the upper-triangular matrix `!![1, b; 0, p]` back
to `p⁻¹ • g`: `(V_p g) ((τ + b) / p) = g (τ + b) = g τ`, by the period-`1` invariance of `g`.
This is the upper-triangular part of the descent of a level-raise
(`Newforms/Descent/LevelRaise.lean`).

## Main results

* `TauCeti.smul_slash_scaleGL_slash_upperTriRep`: for `g` slash-invariant of level `Γ₁(M)`,
  `(p^(1-k) • (g ∣[k] scaleGL p)) ∣[k] !![1, b; 0, p] = p⁻¹ • g`.
* `TauCeti.ModularForm.coe_levelRaise_slash_upperTriRep`: the same for the bundled level-raise
  `ModularForm.levelRaise`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/HeckeDescent.lean`
(`V_p_slash_upper_aux`). The source's `modularFormLevelRaise` is this repository's
`ModularForm.levelRaise`; the statement is re-proved on the underlying function.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {p M : ℕ} [NeZero p] (k : ℤ)

/-- **An upper-triangular matrix slashes a level-raise back to the form**: for `g` slash-invariant
of level `Γ₁(M)` and `V_p g = p^(1-k) • (g ∣[k] scaleGL p)`,
`(V_p g) ∣[k] !![1, b; 0, p] = p⁻¹ • g`, because `(V_p g) ((τ + b) / p) = g (τ + b) = g τ`. -/
theorem smul_slash_scaleGL_slash_upperTriRep {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F ((Gamma1 M).map (mapGL ℝ)) k] (g : F) (b : Fin p) :
    ((p : ℂ) ^ (1 - k) • (⇑g ∣[k] scaleGL p)) ∣[k] (upperTriRep p b : GL (Fin 2) ℚ) =
      (p : ℂ)⁻¹ • ⇑g := by
  funext τ
  have hτ : scaleGL p • (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p b) • τ) =
      ((b : ℝ) +ᵥ τ : ℍ) := by
    ext1
    rw [coe_scaleGL_smul, coe_upperTriRep_smul, UpperHalfPlane.coe_vadd]
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    push_cast
    field_simp
    ring
  rw [slash_upperTriRep_apply, smul_slash_scaleGL_eq, Pi.smul_apply, smul_eq_mul]
  dsimp only
  rw [hτ, SlashInvariantForm.vAdd_apply_of_mem_strictPeriods g τ
    (by simpa using AddSubgroup.nsmul_mem _ (one_mem_strictPeriods_Gamma1_map M) b.val)]

/-- **An upper-triangular matrix slashes the level-raise of a modular form back to the form**:
`(V_p g) ∣[k] !![1, b; 0, p] = p⁻¹ • g`. -/
theorem ModularForm.coe_levelRaise_slash_upperTriRep {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne]
    (hle : 𝒢 ≤ ConjAct.toConjAct (scaleGL p)⁻¹ • (Gamma1 M).map (mapGL ℝ))
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (b : Fin p) :
    ⇑(ModularForm.levelRaise p hle g) ∣[k] (upperTriRep p b : GL (Fin 2) ℚ) = (p : ℂ)⁻¹ • ⇑g := by
  rw [ModularForm.coe_levelRaise, smul_slash_scaleGL_slash_upperTriRep]

end TauCeti
