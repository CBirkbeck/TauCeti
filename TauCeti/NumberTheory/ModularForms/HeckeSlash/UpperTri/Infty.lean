/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.CosetDecomposition
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# Slashing by an upper-triangular representative preserves behaviour at `i∞`

Mathlib's `UpperHalfPlane.IsBoundedAtImInfty.slash` and `IsZeroAtImInfty.slash` carry the
hypothesis `g 1 0 = 0`, so they apply when `g` is upper triangular. (The hypothesis is
sufficient, not necessary — the zero function stays bounded and vanishing after slashing by any
matrix.) This file discharges it for this repository's coset representatives `upperTriRep`.

Having the hypothesis available is why the classical `Tₚ` arguments are organised around
`!![1, b; 0, p]`: these lemmas give the summand-wise step directly, with no further work.

The representatives are rational, while mathlib's lemmas are about the real slash, so each proof
crosses `ModularForm.rat_slash` first — the same bridge `HeckeSlash/Cusps.lean` uses.

## Main results

* `HeckeRing.GL2.isBoundedAtImInfty_slash_upperTriRep`,
  `HeckeRing.GL2.isZeroAtImInfty_slash_upperTriRep`: slashing by a representative preserves
  boundedness, resp. vanishing, at `i∞`.

## Provenance

No code is transcribed. The step corresponds to the analytic core of the AINTLIB
`LeanModularForms` project (Chris Birkbeck, Apache-2.0),
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, whose `heckeT_p_ut_zero_at_cusps` (lines 62-70) needs
exactly this fact about each summand. Here it is stated for a single representative and for
`upperTriRep`, this repository's general-`n` family at `n = 2`, rather than for a transcribed
matrix.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open UpperHalfPlane Matrix

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (p : ℕ)

/-- **Slashing by a representative preserves boundedness at `i∞`.** -/
lemma isBoundedAtImInfty_slash_upperTriRep {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (b : Fin p) :
    IsBoundedAtImInfty (f ∣[k] (upperTriRep p b : GL (Fin 2) ℚ)) :=
  UpperHalfPlane.IsBoundedAtImInfty.rat_slash k (upperTriRep_apply_one_zero p b) hf

/-- **Slashing by a representative preserves vanishing at `i∞`.** -/
lemma isZeroAtImInfty_slash_upperTriRep {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) (b : Fin p) :
    IsZeroAtImInfty (f ∣[k] (upperTriRep p b : GL (Fin 2) ℚ)) :=
  UpperHalfPlane.IsZeroAtImInfty.rat_slash k (upperTriRep_apply_one_zero p b) hf

end HeckeRing.GL2

end
