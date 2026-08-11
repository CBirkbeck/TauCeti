/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Delta0

/-!
# The upper-triangular coset representatives of `T_p`

The classical Hecke operator `T_p` is a sum over the right cosets of the double coset of
`diag(1, p)`, represented by the upper-triangular matrices `[1, b; 0, p]` together with the
diagonal `[p, 0; 0, 1]`. This file introduces the upper-triangular shape and places it in the
semigroup `Δ₀(N)` of `Delta0.lean`, where the Hecke pairs of `Γ₀(N)` and `Γ₁(N)` take their
elements.

Only the upper shape is defined here. The remaining representative is diagonal, so it is already
`HeckeRing.GLn.natDiagGL 2 ![p, 1]`, with `natDiagGL_coe`, `natDiagGL_det` and
`natDiagGL_mem_Delta0_of_coprime` supplying its matrix, determinant and `Δ₀(N)` membership; a
second definition of it here would duplicate that.

The upper representatives lie in `Δ₀(N)` for every `N`, their upper-left entry being `1`. That
distinguishes them from the diagonal representative, whose upper-left entry is `p` and whose
membership is correspondingly conditional on `p`.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), which has the
definition with its coercion and determinant lemmas. The `Δ₀(N)` membership is added here,
`Delta0` being a Tau Ceti module; the proofs are written against the current pin.

## Main definitions

* `HeckeRing.GL2.tpUpper`: the representative `[1, b; 0, p]`.

## Main results

* `HeckeRing.GL2.tpUpper_det`: its determinant is `p`.
* `HeckeRing.GL2.tpUpper_mem_Delta0`: it lies in `Δ₀(N)` for every `N`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open Matrix

namespace HeckeRing.GL2

variable {N : ℕ}

/-- The upper-triangular coset representative `[1, b; 0, p]` of `T_p`, as an element of
`GL₂(ℚ)`. -/
@[expose] noncomputable def tpUpper (p : ℕ) (hp : 0 < p) (b : ℕ) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, (b : ℚ); 0, (p : ℚ)] (by simpa using hp.ne')

/-- The underlying matrix of an upper representative. -/
@[simp]
lemma tpUpper_coe (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (↑(tpUpper p hp b) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (b : ℚ); 0, (p : ℚ)] := rfl

/-- An upper representative has determinant `p`. -/
-- Not `@[simp]`: `simp` already reaches this through `tpUpper_coe` and `Matrix.det_fin_two_of`,
-- so `simpNF` rejects the attribute as redundant. The lemma is kept as the named fact to `rw`.
lemma tpUpper_det (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (↑(tpUpper p hp b) : Matrix (Fin 2) (Fin 2) ℚ).det = p := by
  simp

/-- An upper representative lies in `Δ₀(N)` for every level `N`: its lower-left entry is `0` and
its upper-left entry is `1`, a unit modulo anything. -/
lemma tpUpper_mem_Delta0 (p : ℕ) (hp : 0 < p) (b : ℕ) : tpUpper p hp b ∈ Delta0 N := by
  rw [mem_Delta0_iff]
  refine ⟨!![1, (b : ℤ); 0, (p : ℤ)], ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simpa using (Nat.cast_pos (α := ℚ)).mpr hp
  · simp
  · simp

end HeckeRing.GL2
