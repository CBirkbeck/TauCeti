/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import Mathlib.Tactic.LinearCombination

/-!
# The Möbius index map on `T_p` coset representatives

At a prime `p`, the classical Hecke operator `T_p` is built from the coset representatives
`[1, b; 0, p]` for `b : ZMod p` (together with `[p, 0; 0, 1]`). Right-multiplying one of them by
`σ ∈ SL₂(ℤ)` lands in another such coset, and the resulting index is the Möbius-like expression

`b ↦ (σ₀₁ + b·σ₁₁) / (σ₀₀ + b·σ₁₀)`

read in `ZMod p`, with the degenerate denominator sent to `σ₁₁ / σ₁₀`. This file defines that
index map and shows it is a **permutation** of `ZMod p`, which is what lets a sum over the
representatives be reindexed after a change of variable — the step that makes `T_p` well defined
on modular forms.

The degenerate branch is not a convention chosen for convenience: it is forced. Where
`σ₀₀ + b·σ₁₀` vanishes, the corresponding representative is the one whose bottom row degenerates,
and `σ₁₁ / σ₁₀` is its genuine image. `det σ = 1` is what makes that quotient defined, since
`σ₀₀ + b·σ₁₀` and `σ₁₀` cannot both vanish mod `p` (`lowerLeft_ne_zero_of_moebiusDenom_eq_zero`).

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeT_n.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), where the map is
`moebiusFin'` and only injectivity is proved.

Two things are cleaned up in the migration. The source works in `Fin p`, coercing in and out of
`ZMod p` through `ZMod.val`; since `ZMod p` *is* `Fin p` for `p` prime, indexing by `ZMod p`
directly removes that layer along with the lemmas serving it. And the source's `ZMod`
cancellation helpers predate the current pin: with `Fact p.Prime` in scope `ZMod p` is a field,
so `div_eq_div_iff` and `mul_eq_zero` do that work.

## Main definitions

* `HeckeRing.GL2.moebiusIdx`: the index map `ZMod p → ZMod p` attached to a matrix.

## Main results

* `HeckeRing.GL2.moebiusIdx_injective`: it is injective, for a matrix of determinant `1`.
* `HeckeRing.GL2.moebiusIdxEquiv`: hence a permutation of `ZMod p`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
-/

public section

open Matrix

namespace HeckeRing.GL2

variable {p : ℕ} [Fact p.Prime]

/-- The denominator of the Möbius index map: the reduction of `σ₀₀ + b·σ₁₀` mod `p`.

It is named because both the definition below and every statement about it branch on whether it
vanishes. -/
@[expose] def moebiusDenom (M : Matrix (Fin 2) (Fin 2) ℤ) (b : ZMod p) : ZMod p :=
  (M 0 0 : ZMod p) + b * (M 1 0 : ZMod p)

/-- For a matrix of determinant `1`, the Möbius denominator at `b` and the lower-left entry
cannot both vanish mod `p`: if they did, the determinant would reduce to `0`, not `1`. -/
lemma lowerLeft_ne_zero_of_moebiusDenom_eq_zero {M : Matrix (Fin 2) (Fin 2) ℤ} (hdet : M.det = 1)
    {b : ZMod p} (hb : moebiusDenom M b = 0) : (M 1 0 : ZMod p) ≠ 0 := by
  intro h10
  have hdet' : (M 0 0 : ZMod p) * (M 1 1 : ZMod p) - (M 0 1 : ZMod p) * (M 1 0 : ZMod p) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod p) (det_fin_two M ▸ hdet)
    push_cast at this
    exact this
  have h00 : (M 0 0 : ZMod p) = 0 := by
    have := hb
    rw [moebiusDenom, h10, mul_zero, add_zero] at this
    exact this
  rw [h00, h10, zero_mul, mul_zero, sub_zero] at hdet'
  exact zero_ne_one hdet'

/-- The index map on `T_p` coset representatives induced by right multiplication by `M`.

On the main branch it is the Möbius expression `(σ₀₁ + b·σ₁₁) / (σ₀₀ + b·σ₁₀)` read in `ZMod p`;
where the denominator vanishes it is `σ₁₁ / σ₁₀`, which
`lowerLeft_ne_zero_of_moebiusDenom_eq_zero` shows is defined when `det M = 1`. -/
noncomputable def moebiusIdx (M : Matrix (Fin 2) (Fin 2) ℤ) (b : ZMod p) : ZMod p :=
  if moebiusDenom M b = 0 then (M 1 1 : ZMod p) * (M 1 0 : ZMod p)⁻¹
  else ((M 0 1 : ZMod p) + b * (M 1 1 : ZMod p)) * (moebiusDenom M b)⁻¹

/-- The Möbius index map of a determinant-`1` matrix is injective.

The two-branch case split is genuinely needed. Where both denominators vanish, the difference of
the denominators is `(b₁ - b₂)·σ₁₀` with `σ₁₀ ≠ 0`, giving `b₁ = b₂` directly. Where neither
does, cross-multiplying the equal ratios and expanding leaves `(b₁ - b₂)·det σ`, and `det σ = 1`
finishes it. The mixed cases are impossible: cross-multiplication there would force the
determinant to vanish. -/
lemma moebiusIdx_injective {M : Matrix (Fin 2) (Fin 2) ℤ} (hdet : M.det = 1) :
    Function.Injective (moebiusIdx (p := p) M) := by
  have hdet' : (M 0 0 : ZMod p) * (M 1 1 : ZMod p) - (M 0 1 : ZMod p) * (M 1 0 : ZMod p) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod p) (det_fin_two M ▸ hdet)
    push_cast at this
    exact this
  intro b₁ b₂ heq
  by_cases h₁ : moebiusDenom M b₁ = 0 <;> by_cases h₂ : moebiusDenom M b₂ = 0
  · -- both denominators vanish, so their difference `(b₁ - b₂)·σ₁₀` does; and `σ₁₀ ≠ 0`
    have h10 := lowerLeft_ne_zero_of_moebiusDenom_eq_zero hdet h₁
    have hsub : (b₁ - b₂) * (M 1 0 : ZMod p) = 0 := by
      have hd : moebiusDenom M b₁ - moebiusDenom M b₂ = (b₁ - b₂) * (M 1 0 : ZMod p) := by
        simp only [moebiusDenom]; ring
      rw [h₁, h₂, sub_zero] at hd
      exact hd.symm
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right h10)
  · -- one vanishes and the other does not: cross-multiplying forces `det σ = 0`
    exfalso
    simp only [moebiusIdx, h₁, h₂, ite_true, ite_false] at heq
    have h10 := lowerLeft_ne_zero_of_moebiusDenom_eq_zero hdet h₁
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff h10 h₂] at heq
    simp only [moebiusDenom] at heq
    apply zero_ne_one (α := ZMod p)
    rw [← hdet']
    linear_combination -heq
  · -- the mirror image of the previous case
    exfalso
    simp only [moebiusIdx, h₁, h₂, ite_true, ite_false] at heq
    have h10 := lowerLeft_ne_zero_of_moebiusDenom_eq_zero hdet h₂
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff h₁ h10] at heq
    simp only [moebiusDenom] at heq
    apply zero_ne_one (α := ZMod p)
    rw [← hdet']
    linear_combination heq
  · -- neither vanishes: cross-multiplying leaves `(b₁ - b₂)·det σ`, and `det σ = 1`
    simp only [moebiusIdx, h₁, h₂, ite_false] at heq
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff h₁ h₂] at heq
    simp only [moebiusDenom] at heq
    have hb : (b₁ - b₂) * ((M 0 0 : ZMod p) * (M 1 1 : ZMod p) -
        (M 0 1 : ZMod p) * (M 1 0 : ZMod p)) = 0 := by linear_combination heq
    rw [hdet', mul_one, sub_eq_zero] at hb
    exact hb

/-- The Möbius index map of a determinant-`1` matrix, as a permutation of `ZMod p`.

`ZMod p` is finite, so the injectivity of `moebiusIdx_injective` upgrades to a bijection. This
is the form a reindexing consumes: a sum over the `T_p` coset representatives is unchanged by
the change of variable. -/
@[expose] noncomputable def moebiusIdxEquiv {M : Matrix (Fin 2) (Fin 2) ℤ} (hdet : M.det = 1) :
    Equiv.Perm (ZMod p) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (moebiusIdx_injective hdet))

@[simp]
lemma moebiusIdxEquiv_apply {M : Matrix (Fin 2) (Fin 2) ℤ} (hdet : M.det = 1) (b : ZMod p) :
    moebiusIdxEquiv hdet b = moebiusIdx M b :=
  rfl

end HeckeRing.GL2
