/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The Möbius permutation of `Fin p` attached to an integer matrix

An integer matrix `M` whose determinant is a unit mod `p` permutes `Fin p` by the Möbius rule

`b ↦ (M 0 1 + b * M 1 1) / (M 0 0 + b * M 1 0)  (mod p)`   **where the denominator is nonzero**,

and by `b ↦ M 1 1 / M 1 0` at the **at most one** index where it vanishes. Such an index exists
exactly when `M 1 0 ≢ 0 (mod p)`, and is then `-M 0 0 / M 1 0`; when `M 1 0 ≡ 0` the determinant
forces `M 0 0 ≢ 0`, the denominator never vanishes, and there is no pole at all (take `M = 1`).

The second clause is *not* the first evaluated at a zero denominator: division by zero in `ZMod p`
is `0`, whereas the pole is genuinely carried to the image of `∞` by the projective action.

This is Mathlib's Möbius action of `GL (Fin 2) (ZMod p)` on `OnePoint (ZMod p)` restricted to the
affine part: `Equiv.removeNone` deletes the point at infinity from the induced permutation,
patching the pole to the image of `∞`. Transporting along `ZMod.finEquiv` gives a permutation of
`Fin p`.

The `GL` element and its action are set up over an **arbitrary field**; only the passage to
`Fin p` needs `ZMod p`, where the determinant hypothesis transfers along Mathlib's
`Int.cast_det`.

Nothing here is specific to any one application. The motivating consumer is the `Γ₁(N)`-invariance
of the Hecke operator, where `Fin p` indexes the upper-triangular representatives `!![1, b; 0, p]`.
This permutation is the *index* bookkeeping in that argument; it is **not** by itself the claim
that slashing the representative sum by `M` permutes the summands, which is false in general —
when `M 1 0 ≢ 0 (mod p)` one representative leaves the upper-triangular family altogether, and the
argument there needs the pole case, not a permutation. The statements below mention no Hecke
notion.

## Main definitions

* `TauCeti.moebiusGL`: the `GL (Fin 2) K` element, over any field, whose action gives the rule
  above.
* `TauCeti.moebiusFin`: the reindexing, as an `Equiv.Perm (Fin p)`.

## Main results

* `TauCeti.moebiusGL_smul_some` and `TauCeti.moebiusGL_smul_infty`: the two values of the action,
  in the entries of `M`. The second is what `Equiv.removeNone` splices in at the pole.
* `TauCeti.moebiusGL_smul_some_eq_infty_iff`: the pole sits exactly where the denominator
  `M 0 0 + k * M 1 0` vanishes — the form the divisibility arguments downstream need. It is
  derived from `OnePoint.smul_some_eq_infty_iff`, which this file adds to Mathlib's action API in
  `TauCeti/Topology/Compactification/OnePoint/ProjectiveLine.lean`; the two value lemmas come
  straight from Mathlib's `smul_some_eq_ite` / `smul_infty_eq_ite`.
* `TauCeti.moebiusFin_apply`: the value at an index, with the `ZMod.finEquiv` conjugation
  cancelled, which is how a consumer reaches the value lemmas above without unfolding a body
  that is sealed across the module boundary.

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

namespace TauCeti

open Matrix OnePoint

section Field

variable {K : Type*} [Field K]

/-- **The matrix whose Möbius action is the reindexing.** The entries of `M` are reflected along
the anti-diagonal, so that Mathlib's affine rule
`k ↦ (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1)` reads as
`k ↦ (M 0 1 + k * M 1 1) / (M 0 0 + k * M 1 0)` — on `OnePoint K`, where a vanishing denominator
sends `k` to `∞` rather than to a quotient by zero.

The reflection leaves the determinant alone, so the only hypothesis is invertibility. -/
noncomputable def moebiusGL (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![M 1 1, M 0 1; M 1 0, M 0 0]
    (by
      rw [Matrix.det_fin_two_of]
      rw [Matrix.det_fin_two] at h
      intro hz
      exact h (by linear_combination hz))

@[simp]
lemma moebiusGL_coe (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0) :
    (moebiusGL M h : Matrix (Fin 2) (Fin 2) K) = !![M 1 1, M 0 1; M 1 0, M 0 0] := (rfl)

section Action

-- `[DecidableEq K]` is a hypothesis of the *statements* below, not of their proofs: Mathlib's
-- `instGLAction` — the action they are about — is itself declared under
-- `[Field K] [DecidableEq K]` (`Topology/Compactification/OnePoint/ProjectiveLine.lean:124`), so
-- `g • (k : OnePoint K)` does not elaborate without it. `moebiusGL` above needs no such
-- assumption, and is stated without one.
variable [DecidableEq K]

/-- **The pole of the reindexing.** An affine point `k` goes to `∞` exactly when the denominator
`M 0 0 + k * M 1 0` vanishes. Downstream arguments phrase the exceptional index as a
divisibility, and this is the bridge to it. Proved from `smul_some_eq_infty_iff`.

Deliberately **not** `@[simp]`: with `smul_some_eq_infty_iff` and `moebiusGL_coe` both simp
lemmas, simp already reduces this left-hand side — to `M 1 0 * k + M 0 0 = 0`, the orientation
Mathlib's `smul_some_eq_ite` produces. This lemma exists to offer the other orientation,
`M 0 0 + k * M 1 0 = 0`, which is the one the divisibility arguments downstream are phrased in;
tagging it would put it out of simp normal form. -/
lemma moebiusGL_smul_some_eq_infty_iff (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0) (k : K) :
    moebiusGL M h • (k : OnePoint K) = ∞ ↔ M 0 0 + k * M 1 0 = 0 := by
  rw [smul_some_eq_infty_iff, moebiusGL_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero]
  constructor
  · intro hz; linear_combination hz
  · intro hz; linear_combination hz

/-- **The value at an affine point**, in the entries of `M`. Together with `moebiusGL_smul_infty`
this is the whole action: `Equiv.removeNone` chooses between the two according to whether this
`ite` takes its first branch, which is what `moebiusGL_smul_some_eq_infty_iff` decides.

Not `@[simp]`, matching Mathlib's deliberate choice for `smul_some_eq_ite` / `smul_infty_eq_ite`:
rewriting to an `ite` pre-empts the pole criterion rather than helping it. -/
lemma moebiusGL_smul_some (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0) (k : K) :
    moebiusGL M h • (k : OnePoint K) =
      if M 1 0 * k + M 0 0 = 0 then ∞
      else ((M 1 1 * k + M 0 1) / (M 1 0 * k + M 0 0) : K) := by
  rw [smul_some_eq_ite, moebiusGL_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero]

/-- **The value at the point at infinity**, in the entries of `M`. This is the value
`Equiv.removeNone` splices in at the pole, so it is the ingredient `moebiusGL_smul_some` and the
pole criterion do not supply. -/
lemma moebiusGL_smul_infty (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0) :
    moebiusGL M h • (∞ : OnePoint K) =
      if M 1 0 = 0 then ∞ else ((M 1 1 / M 1 0 : K)) := by
  rw [smul_infty_eq_ite, moebiusGL_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero]

end Action

end Field

variable {p : ℕ} [Fact p.Prime]

/-- **The Möbius reindexing of `Fin p`.** Mathlib's action of `moebiusGL` on `OnePoint (ZMod p)`
is a permutation; `Equiv.removeNone` deletes `∞` from it, patching the pole to the image of `∞`,
and `Equiv.permCongr` along `ZMod.finEquiv` transports the result to `Fin p`. -/
noncomputable def moebiusFin (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ((M.det : ℤ) : ZMod p) ≠ 0) :
    Equiv.Perm (Fin p) :=
  (ZMod.finEquiv p).toEquiv.symm.permCongr
    (Equiv.removeNone (MulAction.toPerm
      (moebiusGL (M.map (Int.cast : ℤ → ZMod p)) (by rwa [Int.cast_det] at h)) :
        Equiv.Perm (OnePoint (ZMod p))))

/-- **The reindexing at an index**, with the conjugation cancelled. `moebiusFin` is
`Equiv.removeNone` of Mathlib's action, conjugated along `ZMod.finEquiv`; reading it this way
strips the conjugation and leaves a statement the value lemmas above apply to directly
(`moebiusGL_smul_some` off the pole, `moebiusGL_smul_infty` at it, with
`moebiusGL_smul_some_eq_infty_iff` deciding which).

This is what a consumer uses: the body of `moebiusFin` is sealed across the module boundary, so
`unfold` is not available to it. -/
lemma moebiusFin_apply (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ((M.det : ℤ) : ZMod p) ≠ 0)
    (b : Fin p) :
    moebiusFin M h b = (ZMod.finEquiv p).symm
      (Equiv.removeNone (MulAction.toPerm
        (moebiusGL (M.map (Int.cast : ℤ → ZMod p)) (by rwa [Int.cast_det] at h)) :
          Equiv.Perm (OnePoint (ZMod p))) ((ZMod.finEquiv p) b)) := by
  simp [moebiusFin, Equiv.permCongr_apply]
end TauCeti
