/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

/-!
# The Möbius action of the shift matrices

The upper-triangular matrix `upperRightHom x = [1, x; 0, 1]` acts on the upper half-plane
as the horizontal shift by `x`.

## Main declarations

* `TauCeti.UpperHalfPlane.upperRightHom_smul`.

## References

* [Mathlib PR #39087](https://github.com/leanprover-community/mathlib4/pull/39087)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public section

open Matrix UpperHalfPlane

namespace TauCeti

/-- The Möbius action of `upperRightHom x = [1, x; 0, 1]` on `ℍ` is the shift `x +ᵥ ·`. -/
theorem upperRightHom_smul (x : ℝ) (τ : ℍ) :
    GeneralLinearGroup.upperRightHom x • τ = x +ᵥ τ := by
  ext1
  rw [coe_smul_of_det_pos (by simp)]
  simp [num, denom, GeneralLinearGroup.upperRightHom_apply, add_comm]

end TauCeti

end
