/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The Möbius reindexing of the upper-triangular representatives

An integer matrix `M` whose determinant is a unit mod `p` permutes the index set `Fin p` of the
upper-triangular representatives `!![1, b; 0, p]`, by the Möbius rule

`b ↦ (M 0 1 + b * M 1 1) / (M 0 0 + b * M 1 0)  (mod p)`.

This is Mathlib's Möbius action of `GL (Fin 2) (ZMod p)` on `OnePoint (ZMod p)` restricted to the
affine part: `Equiv.removeNone` deletes the point at infinity from the induced permutation,
patching the pole to the image of `∞`. Transporting along `ZMod.finEquiv` gives a permutation of
`Fin p`.

It is the combinatorial input to the `Γ₁(N)`-invariance of the Hecke operator: slashing the sum of
representatives by `M` permutes the summands rather than changing them.

## Main definitions

* `HeckeRing.GL2.reindexGL`: the `GL (Fin 2) (ZMod p)` element whose action gives the rule above.
* `HeckeRing.GL2.moebiusFin`: the reindexing, as an `Equiv.Perm (Fin p)`.

## Main results

* `HeckeRing.GL2.reindexGL_smul_coe_eq_infty_iff`: the pole sits exactly where the denominator
  `M 0 0 + k * M 1 0` vanishes mod `p` — the form the divisibility arguments downstream need.

Injectivity is not stated separately: `moebiusFin` is an `Equiv`, so consumers use
`Equiv.injective`.

## Provenance

The statement being realised is AINTLIB's `moebiusFin` / `moebiusFin_injective`
([`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB), commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, lines 124-242, Apache-2.0, Chris Birkbeck).

**No code is transcribed.** The source builds the map by hand as an `if`-split on whether the
denominator vanishes, and proves injectivity by a four-way case analysis resting on five
supporting lemmas. All of that is already Mathlib's: the map is `Equiv.removeNone` applied to
`instGLAction` (`Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean`), and injectivity
is `Equiv.injective`. The entries are permuted along the anti-diagonal because Mathlib's affine
rule is `k ↦ (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1)` (`smul_some_eq_ite`) while the source reads
`M` in the other order.
-/

public section

namespace HeckeRing.GL2

open Matrix OnePoint

variable {p : ℕ} [Fact p.Prime]

/-- **The matrix whose Möbius action is the reindexing.** The entries of `M` are reduced mod `p`
and permuted along the anti-diagonal, so that Mathlib's affine rule
`k ↦ (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1)` reads as
`k ↦ (M 0 1 + k * M 1 1) / (M 0 0 + k * M 1 0)`.

That permutation leaves the determinant alone, so the only hypothesis is that `M` is invertible
mod `p`. -/
@[expose] noncomputable def reindexGL (M : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ((M.det : ℤ) : ZMod p) ≠ 0) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((M 1 1 : ℤ) : ZMod p), ((M 0 1 : ℤ) : ZMod p);
       ((M 1 0 : ℤ) : ZMod p), ((M 0 0 : ℤ) : ZMod p)]
    (by
      rw [Matrix.det_fin_two_of]
      rw [Matrix.det_fin_two] at h
      push_cast at h
      intro hz
      exact h (by linear_combination hz))

@[simp]
lemma reindexGL_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ((M.det : ℤ) : ZMod p) ≠ 0) :
    (reindexGL M h : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![((M 1 1 : ℤ) : ZMod p), ((M 0 1 : ℤ) : ZMod p);
         ((M 1 0 : ℤ) : ZMod p), ((M 0 0 : ℤ) : ZMod p)] := rfl

/-- **The pole of the reindexing.** An affine point `k` goes to `∞` exactly when the denominator
`M 0 0 + k * M 1 0` vanishes mod `p`. Downstream arguments phrase the exceptional index as a
divisibility, and this is the bridge to it. -/
lemma reindexGL_smul_coe_eq_infty_iff (M : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ((M.det : ℤ) : ZMod p) ≠ 0) (k : ZMod p) :
    reindexGL M h • (k : OnePoint (ZMod p)) = ∞ ↔
      ((M 0 0 : ℤ) : ZMod p) + k * ((M 1 0 : ℤ) : ZMod p) = 0 := by
  rw [smul_some_eq_ite, reindexGL_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero]
  split_ifs with hz
  · simp only [true_iff]
    linear_combination hz
  · simp only [coe_ne_infty, false_iff]
    exact fun hk => hz (by linear_combination hk)

/-- **The Möbius reindexing of `Fin p`.** Mathlib's action of `reindexGL M h` on
`OnePoint (ZMod p)` is a permutation; `Equiv.removeNone` deletes `∞` from it, patching the pole to
the image of `∞`, and `Equiv.permCongr` along `ZMod.finEquiv` transports the result to `Fin p`. -/
noncomputable def moebiusFin (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ((M.det : ℤ) : ZMod p) ≠ 0) :
    Equiv.Perm (Fin p) :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  (ZMod.finEquiv p).toEquiv.symm.permCongr
    (Equiv.removeNone (MulAction.toPerm (reindexGL M h) : Equiv.Perm (OnePoint (ZMod p))))

end HeckeRing.GL2
