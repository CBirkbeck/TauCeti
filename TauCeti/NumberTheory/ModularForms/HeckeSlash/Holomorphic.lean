/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic

/-!
# The slash sum preserves holomorphy

`heckeSlashSum` is a finite sum of slashes, so it is holomorphic whenever its argument is. This
is one of the two conditions separating `SlashInvariantForm` from `ModularForm`; the other,
boundedness at the cusps, is not addressed here.

The proof is short because both halves are already in mathlib: `MDifferentiable.slash` for a
single slash, and `MDifferentiable.sum` for the finite sum. The only step particular to this
development is that `heckeSlashSum` slashes by *rational* matrices, so `ModularForm.rat_slash`
restates each summand as a slash by the corresponding real matrix before mathlib's lemma applies.

## Main results

* `HeckeRing.GL2.mdiff_heckeSlashSum`: `heckeSlashSum k D f` is holomorphic when `f` is.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm Manifold

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- **The slash sum of a holomorphic function is holomorphic.** Together with slash-invariance
(`heckeSlashSum_slash_invariant_of_mem_SLnZ`) this supplies one of the two extra conditions a
`ModularForm` carries over a `SlashInvariantForm`; boundedness at the cusps is separate and is
not proved here. -/
lemma mdiff_heckeSlashSum {f : ℍ → ℂ} (hf : MDiff f) : MDiff (heckeSlashSum k D f) := by
  rw [heckeSlashSum_def]
  refine MDifferentiable.sum fun i _ ↦ ?_
  -- each summand slashes by a rational matrix; `rat_slash` restates it at the real image, which
  -- is the form mathlib's `MDifferentiable.slash` applies to
  rw [ModularForm.rat_slash]
  exact hf.slash k _

end HeckeRing.GL2
