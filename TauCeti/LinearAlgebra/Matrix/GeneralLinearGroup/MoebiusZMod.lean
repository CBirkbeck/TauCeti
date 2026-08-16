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

Nothing here is specific to any one application. The motivating consumer is the `Γ₁(N)`-invariance
of the Hecke operator, where `Fin p` indexes the upper-triangular representatives `!![1, b; 0, p]`
and this permutation is what makes slashing the representative sum by `M` permute the summands
rather than change them — but the statements below mention no Hecke notion.

## Main definitions

* `TauCeti.moebiusGL`: the `GL (Fin 2) (ZMod p)` element whose action gives the rule above.
* `TauCeti.moebiusFin`: the reindexing, as an `Equiv.Perm (Fin p)`.

## Main results

* `TauCeti.moebiusGL_smul_coe_eq_infty_iff`: the pole sits exactly where the denominator
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

namespace TauCeti

open Matrix OnePoint

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- **When a Möbius image is the point at infinity.** Mathlib's `smul_some_eq_ite` gives the
*value* of `g • (k : OnePoint K)`; this is the companion criterion for the exceptional case, which
Mathlib does not state. -/
@[simp]
lemma smul_some_eq_infty_iff {g : GL (Fin 2) K} {k : K} :
    g • (k : OnePoint K) = ∞ ↔ (g : Matrix (Fin 2) (Fin 2) K) 1 0 * k +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
  rw [smul_some_eq_ite]
  split_ifs with hz
  · simp [hz]
  · simp [hz]

end Field

variable {p : ℕ} [Fact p.Prime]

/-- **The matrix whose Möbius action is the reindexing.** The entries of `M` are reduced mod `p`
and reflected along the anti-diagonal, so that Mathlib's affine rule
`k ↦ (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1)` reads as
`k ↦ (M 0 1 + k * M 1 1) / (M 0 0 + k * M 1 0)` — on `OnePoint (ZMod p)`, where a vanishing
denominator sends `k` to `∞` rather than to a quotient by zero.

The reflection leaves the determinant alone, so the only hypothesis is invertibility mod `p`.

This is stated over `ZMod p` rather than an arbitrary field **for elaboration cost, not for
mathematical reasons**: with a generic `[Field K]` the `mkOfDetNeZero` application below exceeds
the default heartbeat budget when instantiated at `ZMod p`, and raising `maxHeartbeats` is
forbidden here. The reusable half of the generality is `smul_some_eq_infty_iff` above, which is
stated for every field. -/
noncomputable def moebiusGL (M : Matrix (Fin 2) (Fin 2) ℤ)
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
lemma moebiusGL_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ((M.det : ℤ) : ZMod p) ≠ 0) :
    (moebiusGL M h : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![((M 1 1 : ℤ) : ZMod p), ((M 0 1 : ℤ) : ZMod p);
         ((M 1 0 : ℤ) : ZMod p), ((M 0 0 : ℤ) : ZMod p)] := (rfl)

/-- **The pole of the reindexing.** An affine point `k` goes to `∞` exactly when the denominator
`M 0 0 + k * M 1 0` vanishes mod `p`. Downstream arguments phrase the exceptional index as a
divisibility, and this is the bridge to it. Proved from the field-level
`smul_some_eq_infty_iff`.

Deliberately **not** `@[simp]`: with `smul_some_eq_infty_iff` and `moebiusGL_coe` both simp
lemmas, simp already reduces this left-hand side — to `M 1 0 * k + M 0 0 = 0`, the orientation
Mathlib's `smul_some_eq_ite` produces. This lemma exists to offer the other orientation,
`M 0 0 + k * M 1 0 = 0`, which is the one the divisibility arguments downstream are phrased in;
tagging it would put it out of simp normal form. -/
lemma moebiusGL_smul_coe_eq_infty_iff (M : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ((M.det : ℤ) : ZMod p) ≠ 0) (k : ZMod p) :
    moebiusGL M h • (k : OnePoint (ZMod p)) = ∞ ↔
      ((M 0 0 : ℤ) : ZMod p) + k * ((M 1 0 : ℤ) : ZMod p) = 0 := by
  rw [smul_some_eq_infty_iff, moebiusGL_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero]
  constructor
  · intro hz; linear_combination hz
  · intro hz; linear_combination hz

/-- **The value at an affine point**, in the entries of `M`. Together with `moebiusGL_smul_infty`
this is the whole action: `Equiv.removeNone` chooses between the two according to whether this
`ite` takes its first branch, which is what `moebiusGL_smul_coe_eq_infty_iff` decides. -/
@[simp]
lemma moebiusGL_smul_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ((M.det : ℤ) : ZMod p) ≠ 0)
    (k : ZMod p) :
    moebiusGL M h • (k : OnePoint (ZMod p)) =
      if ((M 1 0 : ℤ) : ZMod p) * k + ((M 0 0 : ℤ) : ZMod p) = 0 then ∞
      else ((((M 1 1 : ℤ) : ZMod p) * k + ((M 0 1 : ℤ) : ZMod p)) /
        (((M 1 0 : ℤ) : ZMod p) * k + ((M 0 0 : ℤ) : ZMod p)) : ZMod p) := by
  rw [smul_some_eq_ite, moebiusGL_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero]

/-- **The value at the point at infinity**, in the entries of `M`. This is the value
`Equiv.removeNone` splices in at the pole, so it is the ingredient `moebiusGL_smul_coe` and the
pole criterion do not supply. -/
@[simp]
lemma moebiusGL_smul_infty (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ((M.det : ℤ) : ZMod p) ≠ 0) :
    moebiusGL M h • (∞ : OnePoint (ZMod p)) =
      if ((M 1 0 : ℤ) : ZMod p) = 0 then ∞
      else ((((M 1 1 : ℤ) : ZMod p)) / (((M 1 0 : ℤ) : ZMod p)) : ZMod p) := by
  rw [smul_infty_eq_ite, moebiusGL_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero]

/-- **The Möbius reindexing of `Fin p`.** Mathlib's action of `moebiusGL M h` on
`OnePoint (ZMod p)` is a permutation; `Equiv.removeNone` deletes `∞` from it, patching the pole to
the image of `∞`, and `Equiv.permCongr` along `ZMod.finEquiv` transports the result to `Fin p`. -/
noncomputable def moebiusFin (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ((M.det : ℤ) : ZMod p) ≠ 0) :
    Equiv.Perm (Fin p) :=
  (ZMod.finEquiv p).toEquiv.symm.permCongr
    (Equiv.removeNone (MulAction.toPerm (moebiusGL M h) : Equiv.Perm (OnePoint (ZMod p))))

/-- The characteristic equation of `moebiusFin`: consumers rewrite through this to Mathlib's
`Equiv.removeNone` and `MulAction.toPerm` API rather than unfolding the definition. Together with
`moebiusGL_smul_coe_eq_infty_iff` (where the pole is) and Mathlib's `smul_some_eq_ite` (the affine
value) this gives the map away from the pole. Computing the value *at* the pole needs
`Equiv.removeNone_none` together with `OnePoint.smul_infty_eq_ite`, since that value is
`removeNone`'s fallback `e none` rather than anything the affine rule sees. -/
lemma moebiusFin_def (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ((M.det : ℤ) : ZMod p) ≠ 0) :
    moebiusFin M h = (ZMod.finEquiv p).toEquiv.symm.permCongr
      (Equiv.removeNone (MulAction.toPerm (moebiusGL M h) : Equiv.Perm (OnePoint (ZMod p)))) :=
  (rfl)

end TauCeti
