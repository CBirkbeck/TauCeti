/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The Möbius reindexing of the upper-triangular representatives

An integer matrix `M` of determinant `1` permutes the index set `Fin p` of the upper-triangular
representatives `!![1, b; 0, p]`, by the Möbius rule

`b ↦ (M 0 1 + b * M 1 1) / (M 0 0 + b * M 1 0)  (mod p)`,

with the quotient `M 1 1 / M 1 0` used when the denominator vanishes. This file defines that map,
`moebiusFin`, and proves it injective — hence a permutation of a finite type. It is the
combinatorial input to the `Γ₁(N)`-invariance of the Hecke operator: slashing the sum of
representatives by `M` permutes the summands rather than changing them.

## Why this is not `Projectivization`

`moebiusFin` is the action of `M` on `ℙ¹(ZMod p)` read in the affine coordinate, the `if` branch
being the point at infinity. Mathlib has the action — `MulAction PGL(ι, K) (ℙ K (ι → K))` in
`Mathlib/LinearAlgebra/Projectivization/Action.lean` — but no affine chart: there is no
`Projectivization ≃ OnePoint` and no `toAffine`/`ofAffine` API anywhere in Mathlib, and
`Projectivization/PSL/PSL2.lean` uses the action only to run Iwasawa's simplicity criterion.
Expressing `moebiusFin` through `Projectivization` would therefore mean building that chart first,
which is strictly more work than the map itself and is not what the consumers need — they need a
term of `Fin p → Fin p` to reindex a `Finset.sum`.

## Main definitions

* `HeckeRing.GL2.moebiusFin`: the reindexing map `Fin p → Fin p` attached to an integer matrix.

## Main results

* `HeckeRing.GL2.moebiusFin_injective`: it is injective when `det M = 1` and `p` is prime.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB), commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), lines 124-242:
`moebiusFin` and `moebiusFin_injective`.

Three of the source's five supporting lemmas are **not** reproduced. `ZMod p` is a field for prime
`p` (`Mathlib/Algebra/Field/ZMod.lean`), which turns them into library calls: "`p ∣ a * b` and
`p ∤ b` gives `p ∣ a`" is `mul_eq_zero`, "congruent with both `< p`" is `ZMod.val_cast_of_lt`, and
the cross-multiplication step is `div_eq_div_iff`. Only the two determinant-driven exclusions carry
content; they appear below as `botLeft_ne_zero_of_add_mul_eq_zero` and `moebiusFin_ne_of_eq_zero`.
-/

public section

namespace HeckeRing.GL2

open Matrix

variable {p : ℕ}

/-- **The Möbius reindexing attached to an integer matrix.** On the affine coordinate `b` this is
`(M 0 1 + b * M 1 1) / (M 0 0 + b * M 1 0)` in `ZMod p`; when that denominator vanishes — the
image is the point at infinity — the value is `M 1 1 / M 1 0` instead.

The definition asks only `NeZero p`, which is what `ZMod.val_lt` needs; primality enters only in
`moebiusFin_injective`. -/
def moebiusFin [NeZero p] (M : Matrix (Fin 2) (Fin 2) ℤ) (b : Fin p) : Fin p :=
  if ((M 0 0 + (b : ℕ) * M 1 0 : ℤ) : ZMod p) = 0 then
    ⟨(((M 1 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  else
    ⟨(((M 0 1 + (b : ℕ) * M 1 1 : ℤ) : ZMod p) *
      ((M 0 0 + (b : ℕ) * M 1 0 : ℤ) : ZMod p)⁻¹).val, ZMod.val_lt _⟩

variable [NeZero p] [Fact p.Prime] {M : Matrix (Fin 2) (Fin 2) ℤ}

omit [NeZero p] in
/-- **A vanishing denominator forces the bottom-left entry to be a unit.** If `M 0 0 + c * M 1 0`
vanishes mod `p` and `M 1 0` did too, then `M 0 0` would vanish as well and `det M` could not be
`1`. -/
private lemma botLeft_ne_zero_of_add_mul_eq_zero
    (hdet : ((M 0 0 : ℤ) : ZMod p) * ((M 1 1 : ℤ) : ZMod p) -
      ((M 0 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) = 1)
    {c : ℤ} (hc : ((M 0 0 + c * M 1 0 : ℤ) : ZMod p) = 0) : ((M 1 0 : ℤ) : ZMod p) ≠ 0 := by
  intro h10
  have h00 : ((M 0 0 : ℤ) : ZMod p) = 0 := by
    push_cast at hc
    rw [h10, mul_zero, add_zero] at hc
    exact hc
  rw [h00, h10, zero_mul, mul_zero, sub_zero] at hdet
  exact zero_ne_one hdet

omit [NeZero p] in
/-- **The two branches of `moebiusFin` never agree.** If one denominator vanishes and the other
does not, cross-multiplying the two candidate values collapses `det M` to `0`. -/
private lemma moebiusFin_ne_of_eq_zero
    (hdet : ((M 0 0 : ℤ) : ZMod p) * ((M 1 1 : ℤ) : ZMod p) -
      ((M 0 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) = 1)
    {c d : ℤ} (hc : ((M 0 0 + c * M 1 0 : ℤ) : ZMod p) = 0)
    (hd : ((M 0 0 + d * M 1 0 : ℤ) : ZMod p) ≠ 0) :
    ((M 1 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹ ≠
      ((M 0 1 + d * M 1 1 : ℤ) : ZMod p) * ((M 0 0 + d * M 1 0 : ℤ) : ZMod p)⁻¹ := by
  intro heq
  have h10 := botLeft_ne_zero_of_add_mul_eq_zero hdet hc
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff h10 hd] at heq
  push_cast at heq hdet
  exact one_ne_zero (show (1 : ZMod p) = 0 by linear_combination heq - hdet)

/-- **The reindexing is injective**, hence a permutation of `Fin p`.

The four cases are on whether each denominator vanishes mod `p`. When both vanish, subtracting
leaves `(b₁ - b₂) * M 1 0 = 0` with `M 1 0` a unit; when neither does, cross-multiplying and using
`det M = 1` leaves `b₁ = b₂`; the mixed cases are impossible by `moebiusFin_ne_of_eq_zero`. -/
theorem moebiusFin_injective (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) :
    Function.Injective (moebiusFin (p := p) M) := by
  have hdetp : ((M 0 0 : ℤ) : ZMod p) * ((M 1 1 : ℤ) : ZMod p) -
      ((M 0 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) (det_fin_two M ▸ hdet)
    push_cast at h
    exact h
  intro b₁ b₂ heq
  have hv := congrArg Fin.val heq
  simp only [moebiusFin] at hv
  split_ifs at hv with h₁ h₂ h₂
  · have hsub : (((b₁ : ℕ) : ZMod p) - ((b₂ : ℕ) : ZMod p)) * ((M 1 0 : ℤ) : ZMod p) = 0 := by
      have h := h₁.trans h₂.symm
      push_cast at h
      linear_combination h
    have hb := sub_eq_zero.mp
      ((mul_eq_zero.mp hsub).resolve_right (botLeft_ne_zero_of_add_mul_eq_zero hdetp h₁))
    have h := congrArg ZMod.val hb
    rwa [ZMod.val_cast_of_lt b₁.isLt, ZMod.val_cast_of_lt b₂.isLt, Fin.val_inj] at h
  · exact absurd (ZMod.val_injective p hv) (moebiusFin_ne_of_eq_zero hdetp h₁ h₂)
  · exact absurd (ZMod.val_injective p hv).symm (moebiusFin_ne_of_eq_zero hdetp h₂ h₁)
  · have hcross : ((M 0 1 + (b₁ : ℕ) * M 1 1 : ℤ) : ZMod p) *
        ((M 0 0 + (b₂ : ℕ) * M 1 0 : ℤ) : ZMod p) =
        ((M 0 1 + (b₂ : ℕ) * M 1 1 : ℤ) : ZMod p) *
        ((M 0 0 + (b₁ : ℕ) * M 1 0 : ℤ) : ZMod p) := by
      rw [← div_eq_div_iff h₁ h₂, div_eq_mul_inv, div_eq_mul_inv]
      exact ZMod.val_injective p hv
    have hb : ((b₁ : ℕ) : ZMod p) = ((b₂ : ℕ) : ZMod p) := by
      push_cast at hcross hdetp
      linear_combination hcross - (((b₁ : ℕ) : ZMod p) - ((b₂ : ℕ) : ZMod p)) * hdetp
    have h := congrArg ZMod.val hb
    rwa [ZMod.val_cast_of_lt b₁.isLt, ZMod.val_cast_of_lt b₂.isLt, Fin.val_inj] at h

end HeckeRing.GL2
