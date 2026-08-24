/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `dotProductBilin` and `dotProductEquiv` occur in the statement and the body below.
public import Mathlib.LinearAlgebra.Matrix.Dual
-- `LinearMap.IsPerfPair` occurs in the statement below.
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

public section

/-!
# The dot product on `ι → R` is a perfect pairing

Mathlib's `dotProductEquiv` identifies `ι → R`, for `ι` finite, with its own dual under the dot
product. This file records the same fact in the form asked for by `LinearMap.IsPerfPair`, so that
the dot product may be used directly as the pairing of a `RootPairing` or a `RootDatum` on `ι → R`.

## Main results

* `TauCeti.dotProductBilin_isPerfPair`: the dot product `dotProductBilin R R` on `ι → R` is a
  perfect pairing of that module with itself.
* `TauCeti.linearIndependent_of_dotProduct_diagonal`: a family whose dot products against a second
  family vanish off the diagonal and are nonzero on it is linearly independent.
-/

namespace TauCeti

open _root_.Matrix

/-- The dot product on `ι → R` is a perfect pairing of that module with itself: it is Mathlib's
`dotProductEquiv` read as a bilinear map. -/
instance dotProductBilin_isPerfPair (R ι : Type*) [CommRing R] [Fintype ι] :
    (dotProductBilin R R : (ι → R) →ₗ[R] (ι → R) →ₗ[R] R).IsPerfPair := by
  classical
  have h : (dotProductBilin R R : (ι → R) →ₗ[R] (ι → R) →ₗ[R] R) =
      (dotProductEquiv R ι).toLinearMap := by
    ext x y
    simp
  rw [h]
  infer_instance

/-- **A family paired diagonally by a second family is linearly independent.** If `v i ⬝ᵥ w j`
vanishes whenever `i ≠ j` and is a nonzero scalar when `i = j`, the `v i` are linearly independent.
The diagonal entries need only be nonzero, not units, so this applies over `ℤ` with diagonal `2`.
The family index `κ` and the coordinate index `ι` are unrelated, and the scalars need not
commute. -/
theorem linearIndependent_of_dotProduct_diagonal {κ ι R : Type*} [Finite κ] [DecidableEq κ]
    [Fintype ι] [Ring R] [NoZeroDivisors R] {v w : κ → ι → R} {c : κ → R}
    (hc : ∀ i, c i ≠ 0) (h : ∀ i j, v i ⬝ᵥ w j = if i = j then c i else 0) :
    LinearIndependent R v := by
  have : Fintype κ := Fintype.ofFinite κ
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  -- pairing the relation with `w j` kills every term but the `j`-th, leaving `g j * c j = 0`
  have hj := congrArg (· ⬝ᵥ w j) hg
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct, h, mul_ite,
    mul_zero] at hj
  rw [Finset.sum_ite_eq' Finset.univ j fun i => g i * c i] at hj
  simp only [Finset.mem_univ, ite_true] at hj
  exact (mul_eq_zero.1 hj).resolve_right (hc j)

end TauCeti
