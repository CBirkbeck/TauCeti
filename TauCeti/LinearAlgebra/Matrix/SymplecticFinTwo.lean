/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The standard symplectic form on a rank-two module, and determinants

For `J = !![0, 1; -1, 0]` and any `2 × 2` matrix `φ` over a commutative ring, `φᵀ J φ = det φ • J`.
The determinant is therefore *recoverable* from the way `φ` scales `J`: if `φᵀ J φ = d • J` for
some scalar `d`, then `d = det φ`.

That recovery is the point of the file. A pairing on a rank-two module which is known to scale by
some quantity under a given endomorphism identifies that quantity as the determinant, without
computing it — and, in particular, without needing the endomorphism to be part of any additive
structure. Only the single endomorphism at hand is involved.

## Main results

* `Matrix.transpose_mul_symJFinTwo_mul`: `φᵀ J φ = det φ • J`.
* `Matrix.det_eq_of_symplectic_scaling`: the scaling coefficient is the determinant.
* `Matrix.det_eq_of_symplectic_adjoint`: the same conclusion from an adjoint `ψ` with
  `φᵀ J = J ψ` and `ψ φ = d • 1`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/PairingDet.lean`, declarations `symJ`, `transpose_mul_symJ_mul`,
`det_eq_of_symplectic_adjoint` and `det_eq_of_symplectic_scaling`. The statements are unchanged;
the names are qualified by the shape of the form, and the source's elliptic-curve commentary
(where the scaling is the Weil pairing's `e(φS, φT) = e(S, T) ^ deg φ` and the conclusion is
`det = deg`) is not reproduced, since no curve occurs in any statement here.
-/

public section

namespace Matrix

variable {F : Type*} [CommRing F]

/-- The standard symplectic form `!![0, 1; -1, 0]` on a rank-two free module. -/
def symJFinTwo (F : Type*) [CommRing F] : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]

@[simp]
theorem symJFinTwo_apply_zero_one : symJFinTwo F 0 1 = 1 := (rfl)

/-- **A `2 × 2` matrix scales the symplectic form by its determinant.** -/
theorem transpose_mul_symJFinTwo_mul (φ : Matrix (Fin 2) (Fin 2) F) :
    φᵀ * symJFinTwo F * φ = φ.det • symJFinTwo F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symJFinTwo, mul_apply, Fin.sum_univ_two, det_fin_two, transpose_apply] <;> ring

/-- **The scaling coefficient is the determinant.** If `φ` scales the symplectic form by `d`,
then `d` is `det φ`. Only `φ` is involved: no adjoint, and no additivity in `φ`. -/
theorem det_eq_of_symplectic_scaling {φ : Matrix (Fin 2) (Fin 2) F} {d : F}
    (hscale : φᵀ * symJFinTwo F * φ = d • symJFinTwo F) : φ.det = d := by
  rw [transpose_mul_symJFinTwo_mul] at hscale
  simpa using congrFun (congrFun hscale 0) 1

/-- **The determinant from an adjoint.** If `ψ` is adjoint to `φ` for the symplectic form, in the
sense that `φᵀ J = J ψ`, and `ψ φ = d • 1`, then `det φ = d`. -/
theorem det_eq_of_symplectic_adjoint {φ ψ : Matrix (Fin 2) (Fin 2) F} {d : F}
    (hadj : φᵀ * symJFinTwo F = symJFinTwo F * ψ)
    (hψφ : ψ * φ = d • (1 : Matrix (Fin 2) (Fin 2) F)) : φ.det = d :=
  det_eq_of_symplectic_scaling <| by rw [hadj, mul_assoc, hψφ, Matrix.mul_smul, mul_one]

end Matrix
