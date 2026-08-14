/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.UpperTriangularDelta0
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# The upper-triangular part of the Hecke operator

The classical `T_p` is a sum of slashes by the representatives `!![1, b; 0, p]` for `b < p`,
together with one further term when `p ∤ N`. This file defines that first sum, `heckeSlashUpperTri`,
and records that it is `ℂ`-linear in `f`.

Why these representatives: mathlib's `IsBoundedAtImInfty.slash` requires `g 1 0 = 0`, so
boundedness of a slash at the cusp `∞` is available exactly for upper-triangular `g`. That is why
the classical arguments run over `!![1, b; 0, p]` rather than over arbitrary coset
representatives. The upper-triangularity itself reads off `upperTriGL_coe` (#3194) and is not
restated here.

## Main definitions

* `HeckeRing.GL2.heckeSlashUpperTri`: the sum `∑ b < p, f ∣[k] !![1, b; 0, p]`.

## Main results

* `HeckeRing.GL2.heckeSlashUpperTri_def`, `HeckeRing.GL2.upperTriRep_def`: the characteristic
  equations, which are the interface since neither definition is `@[expose]`.
* `HeckeRing.GL2.heckeSlashUpperTri_add`, `heckeSlashUpperTri_zero`: additivity in `f`.

## Provenance

The shape is AINTLIB's `heckeT_p_ut`
([`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB), commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck):
`∑ b ∈ Finset.range p, f ∣[k] T_p_upper p hp b`. Restated over this repository's own
representatives — `T_p_upper p _ b` is `upperTriGL` at `n = 2`, `a = ![1, p]` — so AINTLIB's
`T_p_upper` is not reproduced.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix UpperHalfPlane HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (p : ℕ)

/-- The `b`-th upper-triangular representative `!![1, b; 0, p]`, as an element of this
repository's general-`n` family at `a = ![1, p]`. -/
noncomputable def upperTriRep (b : Fin p) : GL (Fin 2) ℚ :=
  upperTriGL ((upperTriEntriesEquivFin p).symm b)

lemma upperTriRep_def (b : Fin p) :
    upperTriRep p b = upperTriGL ((upperTriEntriesEquivFin p).symm b) := (rfl)

/-- **The upper-triangular part of the Hecke operator**: `∑ b < p, f ∣[k] !![1, b; 0, p]`. -/
noncomputable def heckeSlashUpperTri (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ b : Fin p, f ∣[k] upperTriRep p b

lemma heckeSlashUpperTri_def (f : ℍ → ℂ) :
    heckeSlashUpperTri k p f = ∑ b : Fin p, f ∣[k] upperTriRep p b := (rfl)

@[simp] lemma heckeSlashUpperTri_zero : heckeSlashUpperTri k p 0 = 0 := by
  rw [heckeSlashUpperTri]
  exact Finset.sum_eq_zero fun b _ ↦ SlashAction.zero_slash k (upperTriRep p b)

@[simp] lemma heckeSlashUpperTri_add (f g : ℍ → ℂ) :
    heckeSlashUpperTri k p (f + g) = heckeSlashUpperTri k p f + heckeSlashUpperTri k p g := by
  simp [heckeSlashUpperTri, Finset.sum_add_distrib]

end HeckeRing.GL2
