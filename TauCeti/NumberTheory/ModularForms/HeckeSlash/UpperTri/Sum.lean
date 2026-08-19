/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.CosetDecomposition
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# The upper-triangular part of the Hecke operator

The classical `T_p` is a sum of slashes by the representatives `!![1, b; 0, p]` for `b < p`,
together with one further term when `p ∤ N`. This file defines both: the triangular sum
`heckeSlashUpperTri`, and the augmented sum `heckeSlashUpperTriAddDiag` adjoining the diagonal
representative. For each it records `ℂ`-linearity in `f`: zero, addition and scalar multiplication
are preserved. (Linearity in `f` only; neither is yet bundled as a `LinearMap`.)

Why these representatives: mathlib's `IsBoundedAtImInfty.slash` requires `g 1 0 = 0`, so it
applies when `g` is upper triangular. (Sufficient, not necessary — the zero function stays
bounded after slashing by any matrix.) Having that hypothesis to hand is why the classical
arguments are organised around `!![1, b; 0, p]`. It is discharged by `upperTriRep_apply_one_zero`
in
`HeckeRing/GL2/CosetDecomposition.lean`, the `(1, 0)` case of `upperTriGL_apply_eq_zero_of_lt` —
the entrywise description of the representatives is not restated.

## Main definitions

* `HeckeRing.GL2.heckeSlashUpperTri`: the sum `∑ b < p, f ∣[k] !![1, b; 0, p]`.
* `HeckeRing.GL2.heckeSlashUpperTriAddDiag`: that sum together with the diagonal representative
  `!![p, 0; 0, 1]`. For **prime** `p ∤ N`, over `Γ₀(N)` and with trivial character, this is the
  whole `T_p` coset sum; the identification needs both qualifiers and is not proved here.

## Main results

* `HeckeRing.GL2.heckeSlashUpperTri_def` and `heckeSlashUpperTri_apply`: the characteristic
  equation and its pointwise form, the convenient rewrites for turning the operator back into
  its sum.
* `HeckeRing.GL2.heckeSlashUpperTri_zero`, `heckeSlashUpperTri_add`,
  `heckeSlashUpperTri_smul`: linearity in `f`.
* `HeckeRing.GL2.heckeSlashUpperTriAddDiag_def`, `…_apply`, and `…_zero` / `_add` / `_smul`: the
  same interface for the augmented sum.
The representatives themselves, and their upper-triangularity and positive determinant, live in
`HeckeRing/GL2/CosetDecomposition.lean`; this file is only the slash sum built from them.

## Provenance

The shape is AINTLIB's `heckeT_p_ut`
([`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB), commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck):
`∑ b ∈ Finset.range p, f ∣[k] T_p_upper p hp b`. Restated over this repository's own
representatives — `T_p_upper p _ b` is `upperTriGL` at `n = 2`, `a = ![1, p]` — so AINTLIB's
`T_p_upper` is not reproduced.

`heckeSlashUpperTriAddDiag` follows the same project's `heckeT_p_fun` (`HeckeT_p.lean`, lines
110-115), which adjoins a diagonal term to `heckeT_p_ut`, and its prime-`T_p` dispatch
`heckeT_p_all` (`HeckeT_n.lean`, lines 434-437). One deliberate difference, and it is why the
docstrings below qualify the `T_p` claim: AINTLIB's extra term is
`(⇑(diamondOp k ⟨p⟩ f)) ∣[k] T_p_lower p`, carrying the diamond operator, where the term here is
the untwisted `f ∣[k] diagRep p`. The two agree exactly when the nebentypus is trivial. The
twisted form needs `diamondOp`, which this file does not import.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
* [DS] Diamond–Shurman, *A first course in modular forms*, Proposition 5.2.1 — the `p + 1`
  representatives of the `T_p` coset decomposition for `p ∤ N`, the source AINTLIB's
  `heckeT_p_fun` cites for the same statement.
-/

public section

open Matrix UpperHalfPlane HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (p : ℕ)

/-- **The upper-triangular part of the Hecke operator**: `∑ b < p, f ∣[k] !![1, b; 0, p]`. -/
noncomputable def heckeSlashUpperTri (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ b : Fin p, f ∣[k] upperTriRep p b

/-- The defining equation of `heckeSlashUpperTri`: the convenient rewrite for turning the
operator back into its sum. -/
lemma heckeSlashUpperTri_def (f : ℍ → ℂ) :
    heckeSlashUpperTri k p f = ∑ b : Fin p, f ∣[k] upperTriRep p b := (rfl)

/-- The pointwise form of the defining equation: consumers working at a point of `ℍ` — cusp
and `q`-expansion arguments in particular — need the value, not the function. -/
lemma heckeSlashUpperTri_apply (f : ℍ → ℂ) (τ : ℍ) :
    heckeSlashUpperTri k p f τ = ∑ b : Fin p, (f ∣[k] upperTriRep p b) τ := by
  rw [heckeSlashUpperTri_def, Finset.sum_apply]

/-- The sum sends the zero function to zero. -/
@[simp] lemma heckeSlashUpperTri_zero : heckeSlashUpperTri k p 0 = 0 := by
  rw [heckeSlashUpperTri]
  exact Finset.sum_eq_zero fun b _ ↦ SlashAction.zero_slash k (upperTriRep p b)

/-- The sum is additive in `f`, since each slash is. -/
@[simp] lemma heckeSlashUpperTri_add (f g : ℍ → ℂ) :
    heckeSlashUpperTri k p (f + g) = heckeSlashUpperTri k p f + heckeSlashUpperTri k p g := by
  simp [heckeSlashUpperTri, Finset.sum_add_distrib]

/-- **Scalars pass through the sum.** With `heckeSlashUpperTri_add` and
`heckeSlashUpperTri_zero` this is the `ℂ`-linearity of `f ↦ heckeSlashUpperTri k p f`. The
scalar generality matches `ModularForm.rat_smul_slash_of_det_pos`. -/
@[simp] lemma heckeSlashUpperTri_smul {α : Type*} [DistribSMul α ℂ] [IsScalarTower α ℂ ℂ] (c : α)
    (f : ℍ → ℂ) : heckeSlashUpperTri k p (c • f) = c • heckeSlashUpperTri k p f := by
  rw [heckeSlashUpperTri_def, heckeSlashUpperTri_def, Finset.smul_sum]
  exact Finset.sum_congr rfl fun b _ ↦
    ModularForm.rat_smul_slash_of_det_pos k (det_upperTriRep_pos p b) f c

/-- **The upper-triangular sum together with the diagonal term**: the `p` terms of
`heckeSlashUpperTri` plus `f ∣[k] diagRep p`.

⚠ This is **not** claimed to be the full `T_p` coset sum. It is that only for **prime** `p ∤ N`,
over `Γ₀(N)` and with trivial character, where the double coset of `diag(1, p)` has exactly
`p + 1` left cosets. Both qualifiers are load-bearing: with nebentypus `χ` the diagonal term is
`χ(p) • f ∣[k] diagRep p`, and over `Γ₁(N)` the untwisted matrix is not a coset representative at
all. AINTLIB's `heckeT_p_fun` carries precisely that twist — its extra term is
`(⟨p⟩ f) ∣[k] T_p_lower p`.

The count is primality-specific too, and `∑_{d ∣ p} d` is not the number to compare with `p + 1`:
it counts *all* determinant-`p` classes, seven at `p = 4`, spread over more than one double coset.
The double coset of `diag(1, 4)` alone has six left cosets, the seventh class being the scalar
`2 • 1`, which lies in the double coset of `diag(2, 2)`. Six or seven, both exceed the five terms
available here, so the identification is not proved in this file. The definition itself is well
formed for every `p`, which is why no `Nat.Prime` hypothesis is imposed on it.

Every representative summed here is upper triangular — `diagRep` is diagonal — so
`IsBoundedAtImInfty.slash` applies to each term exactly as it does to `heckeSlashUpperTri`. -/
noncomputable def heckeSlashUpperTriAddDiag (f : ℍ → ℂ) : ℍ → ℂ :=
  heckeSlashUpperTri k p f + f ∣[k] diagRep p

/-- The defining equation of `heckeSlashUpperTriAddDiag`, in terms of the partial sum. -/
lemma heckeSlashUpperTriAddDiag_def (f : ℍ → ℂ) :
    heckeSlashUpperTriAddDiag k p f = heckeSlashUpperTri k p f + f ∣[k] diagRep p := (rfl)

/-- The pointwise form, for consumers working at a point of `ℍ`. -/
lemma heckeSlashUpperTriAddDiag_apply (f : ℍ → ℂ) (τ : ℍ) :
    heckeSlashUpperTriAddDiag k p f τ =
      (∑ b : Fin p, (f ∣[k] upperTriRep p b) τ) + (f ∣[k] diagRep p) τ := by
  rw [heckeSlashUpperTriAddDiag_def, Pi.add_apply, heckeSlashUpperTri_apply]

/-- The augmented sum sends the zero function to zero. -/
@[simp] lemma heckeSlashUpperTriAddDiag_zero : heckeSlashUpperTriAddDiag k p 0 = 0 := by
  rw [heckeSlashUpperTriAddDiag_def, heckeSlashUpperTri_zero, SlashAction.zero_slash, add_zero]

/-- The augmented sum is additive in `f`, since each slash is. -/
@[simp] lemma heckeSlashUpperTriAddDiag_add (f g : ℍ → ℂ) :
    heckeSlashUpperTriAddDiag k p (f + g) =
      heckeSlashUpperTriAddDiag k p f + heckeSlashUpperTriAddDiag k p g := by
  rw [heckeSlashUpperTriAddDiag_def, heckeSlashUpperTriAddDiag_def,
    heckeSlashUpperTriAddDiag_def, heckeSlashUpperTri_add, SlashAction.add_slash]
  ring

/-- **Scalars pass through the augmented sum.** With `heckeSlashUpperTriAddDiag_add` and
`heckeSlashUpperTriAddDiag_zero` this is the `ℂ`-linearity of
`f ↦ heckeSlashUpperTriAddDiag k p f`. Unconditional in `p`, matching
`heckeSlashUpperTri_smul`: `det_diagRep_pos` needs no positivity, since `natDiagGL`'s junk
value is the identity. -/
@[simp] lemma heckeSlashUpperTriAddDiag_smul {α : Type*} [DistribSMul α ℂ]
    [IsScalarTower α ℂ ℂ]
    (c : α) (f : ℍ → ℂ) :
      heckeSlashUpperTriAddDiag k p (c • f) = c • heckeSlashUpperTriAddDiag k p f := by
  rw [heckeSlashUpperTriAddDiag_def, heckeSlashUpperTriAddDiag_def, heckeSlashUpperTri_smul,
    smul_add, ModularForm.rat_smul_slash_of_det_pos k (det_diagRep_pos p) f c]

end HeckeRing.GL2
