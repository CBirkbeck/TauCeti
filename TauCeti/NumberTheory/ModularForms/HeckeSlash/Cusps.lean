/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.BoundedAtCusp
public import TauCeti.NumberTheory.ModularForms.CuspsRat
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic

/-!
# The Hecke slash sum vanishes, and is bounded, at the cusps

`heckeSlashSum` is a finite sum of slashes, so its behaviour at a cusp follows from that of its
summands. A slash is zero at `c` exactly when the original function is zero at `g • c`
(`OnePoint.IsZeroAt.smul_iff`), and `g • c` is again a cusp because the representatives are
rational (`isCusp_smul_map_ratCast`). So a function vanishing at every cusp has a slash sum
vanishing at every cusp, whatever representatives were chosen.

This is the step the Layer 2 statement "`Tₙ` preserves `S_k`" rests on. The cusp hypothesis is
the one a `CuspForm` actually supplies through `zero_at_cusps'`, which only gives vanishing where
`IsCusp c Γ` holds.

## Main results

* `HeckeRing.GL2.isZeroAt_heckeSlashSum`: the slash sum of a function vanishing at every cusp
  vanishes at every cusp.
* `HeckeRing.GL2.isBoundedAt_heckeSlashSum`: the same for boundedness.

## Provenance

The shape is AINTLIB's `heckeT_p_ut_zero_at_cusps`
([`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean`](https://github.com/CBirkbeck/AINTLIB)
lines 62-71, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck),
which runs the same argument by hand with `Finset.sum_induction` over its own representatives.
Here the induction is `OnePoint.IsZeroAt.sum`, and the statement is about this repository's
`heckeSlashSum`.
-/

public section

namespace HeckeRing.GL2

open UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- **The slash sum vanishes at every cusp** when the function does. Each summand `f ∣[k] g` is
zero at the cusp `c` because `f` is zero at the cusp `g • c`, and `OnePoint.IsZeroAt` is closed
under finite sums. -/
lemma isZeroAt_heckeSlashSum {f : ℍ → ℂ}
    (hf : ∀ c : OnePoint ℝ, IsCusp c 𝒮ℒ → c.IsZeroAt f k) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt (heckeSlashSum k D f) k := by
  rw [heckeSlashSum_def]
  exact OnePoint.IsZeroAt.sum fun i _ ↦
    OnePoint.IsZeroAt.smul_iff.mp (hf _ (isCusp_smul_map_ratCast _ hc))

/-- **The slash sum is bounded at every cusp** when the function is. -/
lemma isBoundedAt_heckeSlashSum {f : ℍ → ℂ}
    (hf : ∀ c : OnePoint ℝ, IsCusp c 𝒮ℒ → c.IsBoundedAt f k) {c : OnePoint ℝ}
    (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt (heckeSlashSum k D f) k := by
  rw [heckeSlashSum_def]
  exact OnePoint.IsBoundedAt.sum fun i _ ↦
    OnePoint.IsBoundedAt.smul_iff.mp (hf _ (isCusp_smul_map_ratCast _ hc))

end HeckeRing.GL2

end
