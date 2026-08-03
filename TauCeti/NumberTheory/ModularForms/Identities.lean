/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ModularForms.Identities
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.NumberTheory.ModularForms.Cusps

/-!
# The slash action of powers of `T`

Acting by a power of the translation matrix `T` through the weight-`k` slash action is
precomposition with the corresponding horizontal shift.

## Main declarations

* `TauCeti.slash_T_zpow_apply`.

## References

* [Mathlib PR #39087](https://github.com/leanprover-community/mathlib4/pull/39087)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public section

open UpperHalfPlane Matrix Matrix.SpecialLinearGroup ModularForm

open scoped MatrixGroups ModularForm

namespace TauCeti

/-- Acting on a function `g : ℍ → ℂ` by `T ^ j` via the weight `k` slash action is the
shift `τ ↦ g ((j : ℝ) +ᵥ τ)`. -/
lemma slash_T_zpow_apply (k j : ℤ) (g : ℍ → ℂ) (τ : ℍ) :
    (g ∣[k] ((ModularGroup.T : SL(2, ℤ))^j : GL (Fin 2) ℝ)) τ = g ((j : ℝ) +ᵥ τ) := by
  -- The coercion of `T ^ j` is definitionally the image of `T` under `mapGL`, raised to
  -- `j`; `change` exposes that spelling once.
  change (g ∣[k] ((mapGL ℝ (ModularGroup.T : SL(2, ℤ)))^j)) τ = _
  rw [← map_zpow, ModularGroup.mapGL_T_zpow_eq_upperRightHom, slash_apply,
    upperRightHom_smul]
  simp [σ, denom, GeneralLinearGroup.val_det_apply]

end TauCeti

end
