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
* `Matrix.prod_eq_det_of_mul_mul_eq_diagonal`: the product of a diagonalisation's diagonal
  entries is the determinant.
* `Matrix.exists_SL_mul_mul_eq_of_mul_mul_eq`: two matrices carried to a common value by
  `SL`-transformations are themselves `SL`-equivalent.
-/

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

public section

/-- **Inverting a two-sided unimodular transformation.** -/
theorem inv_mul_mul_inv_of_mul_mul_eq {S : Type*} [Semiring S]
    {A B : Matrix ι ι S} (L R : GeneralLinearGroup ι S)
    (h : (L : Matrix ι ι S) * A * (R : Matrix ι ι S) = B) :
    (↑L⁻¹ : Matrix ι ι S) * B * (↑R⁻¹ : Matrix ι ι S) = A := by
  rw [← h]
  simp [Matrix.mul_assoc]

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
    {A B : Matrix ι ι S} {LA RA LB RB : SpecialLinearGroup ι S}
    (h : (LA : Matrix ι ι S) * A * (RA : Matrix ι ι S) =
      (LB : Matrix ι ι S) * B * (RB : Matrix ι ι S)) :
    ∃ P Q : SpecialLinearGroup ι S,
      (P : Matrix ι ι S) * A * (Q : Matrix ι ι S) = B := by
  refine ⟨LB⁻¹ * LA, RA * RB⁻¹, ?_⟩
  -- `simp` normalises the `SL` inverse to `adjugate`; `inv_def` with `det = 1` takes the
  -- `GL` inverse the same way, so the two sides meet.
  simpa [SpecialLinearGroup.coe_mul, Matrix.mul_assoc, Matrix.inv_def] using
    inv_mul_mul_inv_of_mul_mul_eq LB.toGL RB.toGL h.symm

end

end Matrix
