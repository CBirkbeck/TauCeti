/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Delta0

/-!
# The coset representatives of `T_p`

The classical Hecke operator `T_p` is a sum over the `p + 1` right cosets of the double coset of
`diag(1, p)`, represented by

`[1, b; 0, p]` for `b = 0, …, p - 1`,  together with  `[p, 0; 0, 1]`.

This file introduces those two shapes as elements of `GL₂(ℚ)` and records what places them in the
semigroup `Δ₀(N)` of `Delta0.lean`, which is where the Hecke pairs of `Γ₀(N)` and `Γ₁(N)` take
their elements.

The asymmetry in the two membership statements is the arithmetic of the operator, not an artefact.
The upper representatives lie in `Δ₀(N)` for **every** `N`: their upper-left entry is `1`, a unit
modulo anything. The lower representative has upper-left entry `p`, so it lies in `Δ₀(N)` exactly
when `p` is a unit modulo `N` — and at `p ∣ N` its coset drops out, leaving the `p` upper cosets
alone. That is the bad-prime operator classically written `U_p`, and it is why the count is
`p + 1` at good primes and `p` at bad ones.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), which has the two
definitions with their coercion and determinant lemmas. The `Δ₀(N)` membership is added here,
`Delta0` being a Tau Ceti module; the proofs are written against the current pin.

## Main definitions

* `HeckeRing.GL2.tpUpper`, `HeckeRing.GL2.tpLower`: the two shapes of representative.

## Main results

* `HeckeRing.GL2.tpUpper_det`, `HeckeRing.GL2.tpLower_det`: both have determinant `p`.
* `HeckeRing.GL2.tpUpper_mem_Delta0`: the upper representatives lie in `Δ₀(N)` for every `N`.
* `HeckeRing.GL2.tpLower_mem_Delta0`: the lower one does exactly when `p` is a unit mod `N`.

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

/-- The remaining coset representative `[p, 0; 0, 1]` of `T_p`, as an element of `GL₂(ℚ)`. -/
@[expose] noncomputable def tpLower (p : ℕ) (hp : 0 < p) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![(p : ℚ), 0; 0, 1] (by simpa using hp.ne')

/-- The underlying matrix of an upper representative. -/
@[simp]
lemma tpUpper_coe (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (↑(tpUpper p hp b) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (b : ℚ); 0, (p : ℚ)] := rfl

/-- The underlying matrix of the lower representative. -/
@[simp]
lemma tpLower_coe (p : ℕ) (hp : 0 < p) :
    (↑(tpLower p hp) : Matrix (Fin 2) (Fin 2) ℚ) = !![(p : ℚ), 0; 0, 1] := rfl

/-- An upper representative has determinant `p`. Together with `tpLower_det` this is what makes
the two shapes representatives for the *same* double coset. -/
-- Not `@[simp]`: `simp` already reaches this through `tpUpper_coe` and `Matrix.det_fin_two_of`,
-- so `simpNF` rejects the attribute as redundant. The lemma is kept as the named fact to `rw`.
lemma tpUpper_det (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (↑(tpUpper p hp b) : Matrix (Fin 2) (Fin 2) ℚ).det = p := by
  simp

/-- The lower representative has determinant `p`, matching `tpUpper_det`. -/
-- Not `@[simp]`, for the same reason as `tpUpper_det`.
lemma tpLower_det (p : ℕ) (hp : 0 < p) :
    (↑(tpLower p hp) : Matrix (Fin 2) (Fin 2) ℚ).det = p := by
  simp

/-- The upper representatives lie in `Δ₀(N)` for every level `N`: the lower-left entry is `0` and
the upper-left entry is `1`, a unit modulo anything. -/
lemma tpUpper_mem_Delta0 (p : ℕ) (hp : 0 < p) (b : ℕ) : tpUpper p hp b ∈ Delta0 N := by
  rw [mem_Delta0_iff]
  refine ⟨!![1, (b : ℤ); 0, (p : ℤ)], ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simpa using (Nat.cast_pos (α := ℚ)).mpr hp
  · simp
  · simp

/-- The lower representative lies in `Δ₀(N)` exactly when `p` is a unit modulo `N` — its
upper-left entry is `p`. At `p ∣ N` this coset is absent, which is the bad-prime operator. -/
lemma tpLower_mem_Delta0 (p : ℕ) (hp : 0 < p) (hpN : IsUnit (p : ZMod N)) :
    tpLower p hp ∈ Delta0 N := by
  rw [mem_Delta0_iff]
  refine ⟨!![(p : ℤ), 0; 0, 1], ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simpa using (Nat.cast_pos (α := ℚ)).mpr hp
  · simp
  · simpa using hpN

end HeckeRing.GL2
