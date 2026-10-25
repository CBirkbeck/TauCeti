/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Toeplitz

/-!
# Laurent-monomial Toeplitz checks

Laurent monomials give single diagonals in the Hardy-basis matrix. Both conventions are explicit:
row minus column has coefficient index `n`, and column minus row has coefficient index `-n`.
The symbols of degrees one and minus one act as the unilateral shift and its backward shift.
These supply the scalar monomial and shift computations of ToeplitzOperators target T6.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- The Laurent monomial of degree `n` has ones on the Hardy-matrix diagonal `i - j = n`. -/
theorem inner_hardyBasis_toeplitz_fourierLp (n : ℤ) (i j : ℕ) :
    ⟪hardyBasis i, toeplitz (fourierLp (T := 1) ∞ n) (hardyBasis j)⟫_ℂ =
      if (i : ℤ) - j = n then 1 else 0 := by
  rw [inner_hardyBasis_toeplitz_hardyBasis,
    fourierCoeff_congr_ae (coeFn_fourierLp ∞ n), fourierCoeff_fourier, Pi.single_apply]

/-- In the column-minus-row convention the monomial of degree `n` has coefficient index `-n`. -/
theorem inner_hardyBasis_toeplitz_fourierLp_reverse (n : ℤ) (i j : ℕ) :
    ⟪hardyBasis i, toeplitz (fourierLp (T := 1) ∞ n) (hardyBasis j)⟫_ℂ =
      if (j : ℤ) - i = -n then 1 else 0 := by
  rw [inner_hardyBasis_toeplitz_fourierLp]
  have h : ((i : ℤ) - j = n) ↔ ((j : ℤ) - i = -n) := by omega
  simp only [h]

/-- The degree-one monomial acts as the forward unilateral shift on the Hardy basis. -/
theorem toeplitz_fourierLp_one_hardyBasis (j : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ 1) (hardyBasis j) = hardyBasis (j + 1) := by
  apply hardyBasis.repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply, inner_hardyBasis_toeplitz_fourierLp,
    HilbertBasis.repr_self, lp.single_apply, Pi.single_apply]
  have h : ((i : ℤ) - j = 1) ↔ i = j + 1 := by omega
  simp only [h]

/-- The degree-minus-one monomial kills the constant Hardy-basis vector. -/
theorem toeplitz_fourierLp_neg_one_hardyBasis_zero :
    toeplitz (fourierLp (T := 1) ∞ (-1)) (hardyBasis 0) = 0 := by
  apply hardyBasis.repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply, inner_hardyBasis_toeplitz_fourierLp]
  have h : ¬ (i : ℤ) - (0 : ℕ) = -1 := by omega
  simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, ite_eq_right h]

/-- The degree-minus-one monomial acts as the backward unilateral shift on positive modes. -/
theorem toeplitz_fourierLp_neg_one_hardyBasis_succ (j : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ (-1)) (hardyBasis (j + 1)) = hardyBasis j := by
  apply hardyBasis.repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply, inner_hardyBasis_toeplitz_fourierLp,
    HilbertBasis.repr_self, lp.single_apply, Pi.single_apply]
  have h : ((i : ℤ) - (j + 1) = -1) ↔ i = j := by omega
  simp only [Nat.cast_add, Nat.cast_one, h]

end TauCeti
