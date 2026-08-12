/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Delta0
public import TauCeti.NumberTheory.HeckeRing.GLn.CosetDecomposition

/-!
# Upper-triangular coset representatives at level `N`

`GLn/CosetDecomposition.lean` builds the representatives `diag(a) · U(B)` of the left cosets in
`SL_n(ℤ) · diag(a) · SL_n(ℤ)`, indexed by the bounded entry assignments `UpperTriEntries n a`.
This file places them, at `n = 2`, in the semigroup `Δ₀(N)` where the Hecke pairs of `Γ₀(N)` and
`Γ₁(N)` take their elements.

The condition is the same one the diagonal case needs: the entries below the diagonal vanish, so
beyond integrality and positivity of the determinant only the upper-left entry has to be a unit
modulo `N`, and that entry is `a₀` whatever `B` is. So
`HeckeRing.GL2.natDiagGL_mem_Delta0_of_coprime` is the case `B = 0` of the lemma proved here.

The `T_p` application is `a = ![1, p]`: the `p` representatives `[1, b; 0, p]` are
`upperTriGL B` for `B` the single entry `b ∈ Fin p`, and they lie in `Δ₀(N)` for **every** level
`N`, since `a₀ = 1` is a unit modulo anything. The remaining representative of `T_p` is the
diagonal `[p, 0; 0, 1] = natDiagGL 2 ![p, 1]`, whose membership is `natDiagGL_mem_Delta0_of_coprime`
and is genuinely conditional on `p`. That asymmetry — `p + 1` representatives, `p` of them
unconditional and one not — is a fact about the cosets, not an artefact of the encoding.

## Main results

* `HeckeRing.GL2.upperTriGL_mem_Delta0_of_coprime`: `diag(a) · U(B) ∈ Δ₀(N)` when `a₀` is
  coprime to `N`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open Matrix

namespace HeckeRing.GL2

open HeckeRing.GLn

variable (N : ℕ)

/-- An upper-triangular coset representative `diag(a) · U(B)` lies in `Δ₀(N)` as soon as its
upper-left entry `a₀` is coprime to the level: everything below the diagonal vanishes, so the
only condition with content is that `a₀` be a unit modulo `N`, and `B` does not affect it.

The diagonal case `B = 0` is `natDiagGL_mem_Delta0_of_coprime`. -/
lemma upperTriGL_mem_Delta0_of_coprime {a : Fin 2 → ℕ} (ha : ∀ i, 0 < a i)
    (hgcd : Nat.Coprime (a 0) N) (B : UpperTriEntries 2 a) :
    upperTriGL B ∈ Delta0 N := by
  refine (mem_Delta0_iff N).mpr
    ⟨Matrix.of fun i j ↦ (a i : ℤ) * unitriMat B i j, ?_, ?_, ?_, ?_⟩
  · ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [upperTriGL_apply_lt ha B h]
      simp [unitriMat_apply_lt B h]
    · rw [upperTriGL_apply_diag ha B]
      simp
    · rw [upperTriGL_apply_eq_zero_of_lt ha B h]
      simp [unitriMat_apply_eq_zero_of_lt B h]
  · rw [upperTriGL_def, Units.val_mul, Matrix.det_mul,
      det_eq_one_of_mem_SLnZ 2 (coe_mem_SLnZ 2 (unitriSL B)), mul_one]
    exact natDiagGL_det_pos 2 a ha
  · simp
  · simpa using (ZMod.isUnit_iff_coprime (a 0) N).mpr hgcd

end HeckeRing.GL2
