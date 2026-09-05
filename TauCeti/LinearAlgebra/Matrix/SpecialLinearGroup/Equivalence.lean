/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Two-sided unimodular equivalence of matrices

Matrices related by `L * A * R` with `L` and `R` unimodular. Nothing here assumes a Smith
normal form or a divisibility chain along a diagonal, so these facts sit below that theory
rather than inside it, and hold over an arbitrary finite index type.

## Main results

* `Matrix.inv_mul_mul_inv_of_mul_mul_eq`: inverting a two-sided unimodular transformation.
* `Matrix.inv_coe_eq_coe_inv`: the `SL` inverse agrees with the matrix inverse of the
  coercion.
* `Matrix.prod_eq_det_of_mul_mul_eq_diagonal`: the product of a diagonalisation's diagonal
  entries is the determinant.
* `Matrix.exists_SL_mul_mul_eq_of_mul_mul_eq`: two matrices carried to a common value by
  `SL`-transformations are themselves `SL`-equivalent.
-/

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

public section

/-- **Inverting a two-sided unimodular transformation.** The rows and columns are transformed
independently, so they need not share an index type. -/
theorem inv_mul_mul_inv_of_mul_mul_eq {S : Type*} [Semiring S]
    {A B : Matrix ι κ S} (L : GeneralLinearGroup ι S) (R : GeneralLinearGroup κ S)
    (h : (L : Matrix ι ι S) * A * (R : Matrix κ κ S) = B) :
    (↑L⁻¹ : Matrix ι ι S) * B * (↑R⁻¹ : Matrix κ κ S) = A := by
  -- with the rows and columns indexed separately, the two cancellations are named rather
  -- than left to `simp`, which no longer matches them across the differing index types
  have hL : (↑L⁻¹ : Matrix ι ι S) * (L : Matrix ι ι S) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hR : (R : Matrix κ κ S) * (↑R⁻¹ : Matrix κ κ S) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← h]
  simp only [Matrix.mul_assoc, hR, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hL, Matrix.one_mul]

/-- **The `SL` inverse agrees with the matrix inverse of the coercion.** Determinant `1` makes
the coercion of `M⁻¹` a right inverse of the coercion of `M`, which pins the matrix inverse
without unfolding how either inverse is represented. -/
theorem inv_coe_eq_coe_inv {n : Type*} [Fintype n] [DecidableEq n] {S : Type*} [CommRing S]
    (M : SpecialLinearGroup n S) :
    ((M : Matrix n n S))⁻¹ = ((M⁻¹ : SpecialLinearGroup n S) : Matrix n n S) :=
  Matrix.inv_eq_right_inv (by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one])

/-- **The product of a diagonalisation's diagonal entries is the determinant.** Both `SL`
factors have determinant `1`, so taking determinants through `L * A * R = diagonal d` leaves
the product of the diagonal.

No divisibility chain is assumed, so `d` need not be the invariant factors. -/
theorem prod_eq_det_of_mul_mul_eq_diagonal {S : Type*} [CommRing S]
    {A : Matrix ι ι S} {L R : SpecialLinearGroup ι S} {d : ι → S}
    (h : (L : Matrix ι ι S) * A * (R : Matrix ι ι S) = Matrix.diagonal d) :
    ∏ i, d i = A.det := by
  have hdet := congrArg Matrix.det h
  simp only [Matrix.det_mul, L.2, R.2, one_mul, mul_one, Matrix.det_diagonal] at hdet
  exact hdet.symm

/-- **Matrices sharing an `SL`-transform are `SL`-equivalent.** If `L_A A R_A = L_B B R_B`
then `L_B⁻¹ L_A` and `R_A R_B⁻¹` carry `A` to `B`.

Pure group algebra: nothing is assumed about the common value, which need not be diagonal.
Callers holding two diagonalisations with equal diagonals compose them into this single
hypothesis. -/
theorem exists_SL_mul_mul_eq_of_mul_mul_eq {S : Type*} [CommRing S]
    {A B : Matrix ι κ S} {LA LB : SpecialLinearGroup ι S} {RA RB : SpecialLinearGroup κ S}
    (h : (LA : Matrix ι ι S) * A * (RA : Matrix κ κ S) =
      (LB : Matrix ι ι S) * B * (RB : Matrix κ κ S)) :
    ∃ (P : SpecialLinearGroup ι S) (Q : SpecialLinearGroup κ S),
      (P : Matrix ι ι S) * A * (Q : Matrix κ κ S) = B := by
  refine ⟨LB⁻¹ * LA, RA * RB⁻¹, ?_⟩
  simpa [SpecialLinearGroup.coe_mul, Matrix.mul_assoc, inv_coe_eq_coe_inv] using
    inv_mul_mul_inv_of_mul_mul_eq LB.toGL RB.toGL h.symm

end

end Matrix
