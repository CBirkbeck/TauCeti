/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Toeplitz.Basic

/-!
# Laurent-monomial Toeplitz checks

Laurent monomials give single diagonals in the Hardy-basis matrix. Both conventions are explicit:
row minus column has coefficient index `n`, and column minus row has coefficient index `-n`.
The symbols of degrees one and minus one act as the unilateral shift and its backward shift.
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

/-- The Laurent monomial of degree `n` shifts a Hardy basis vector by `n`, or annihilates it
when the resulting degree is negative. -/
theorem toeplitz_fourierLp_hardyBasis (n : ℤ) (j : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ n) (hardyBasis j) =
      if 0 ≤ (j : ℤ) + n then hardyBasis (((j : ℤ) + n).toNat) else 0 := by
  by_cases h : 0 ≤ (j : ℤ) + n
  · simp only [h, ite_true]
    apply hardyBasis.repr.injective
    ext i
    rw [HilbertBasis.repr_apply_apply, inner_hardyBasis_toeplitz_fourierLp,
      HilbertBasis.repr_self, lp.single_apply, Pi.single_apply]
    have heq : (((i : ℤ) - j = n) ↔ i = ((j : ℤ) + n).toNat) := by omega
    simp only [heq]
  · simp only [h, ite_false]
    apply hardyBasis.repr.injective
    ext i
    rw [HilbertBasis.repr_apply_apply, inner_hardyBasis_toeplitz_fourierLp]
    have hne : ¬ (i : ℤ) - j = n := by omega
    simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, ite_eq_right hne]

/-- The degree-one monomial acts as the forward unilateral shift on the Hardy basis. -/
@[simp]
theorem toeplitz_fourierLp_one_hardyBasis (j : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ 1) (hardyBasis j) = hardyBasis (j + 1) := by
  have h : 0 ≤ (j : ℤ) + 1 := by omega
  have hk : (((j : ℤ) + 1).toNat) = j + 1 := by omega
  simpa only [h, ite_true, hk] using toeplitz_fourierLp_hardyBasis 1 j

/-- The degree-minus-one monomial kills the constant Hardy-basis vector. -/
@[simp]
theorem toeplitz_fourierLp_neg_one_hardyBasis_zero :
    toeplitz (fourierLp (T := 1) ∞ (-1)) (hardyBasis 0) = 0 := by
  simpa using toeplitz_fourierLp_hardyBasis (-1) 0

/-- The degree-minus-one monomial acts as the backward unilateral shift on positive modes. -/
@[simp]
theorem toeplitz_fourierLp_neg_one_hardyBasis_succ (j : ℕ) :
    toeplitz (fourierLp (T := 1) ∞ (-1)) (hardyBasis (j + 1)) = hardyBasis j := by
  have h : 0 ≤ ((j + 1 : ℕ) : ℤ) + (-1) := by omega
  have hk : ((((j + 1 : ℕ) : ℤ) + (-1)).toNat) = j := by omega
  simpa only [h, ite_true, hk] using toeplitz_fourierLp_hardyBasis (-1) (j + 1)

end TauCeti
