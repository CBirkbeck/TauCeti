/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Change of scalars on general linear groups

`Matrix.GeneralLinearGroup.map f : GL n R →* GL n S` applies a ring hom `f : R →+* S` entrywise.
Mathlib gives its functoriality (`map_id`, `map_comp`, `map_comp_apply`) but says nothing about
injectivity, which is what a construction transporting a group of matrices along a change of
scalars needs.

The instance used throughout the modular-forms development is `ℚ → ℝ` at `n = 2`: rational matrix
data does not act on the upper half-plane and real matrix data does. It is spelled
`Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)` at each use rather than abbreviated.

## Main results

* `Matrix.GeneralLinearGroup.map_injective`: entrywise application of an injective ring hom is
  injective on general linear groups.
-/

public section

open Matrix

open scoped MatrixGroups

namespace Matrix.GeneralLinearGroup

variable {n R S : Type*} [DecidableEq n] [Fintype n] [CommRing R] [CommRing S]

/-- **Entrywise application of an injective ring hom is injective on `GL n`.** A matrix over `R`
is determined by its image over `S`, and a unit by its underlying matrix. -/
theorem map_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := n) f) :=
  Units.map_injective (Matrix.map_injective hf)

end Matrix.GeneralLinearGroup

