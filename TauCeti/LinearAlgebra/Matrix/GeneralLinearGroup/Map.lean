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

The one instance of `map` that is used throughout is `ℚ → ℝ` at `n = 2`: rational matrix data does
not act on the upper half-plane and real matrix data does, so it is named here rather than spelled
out at each use.

## Main definitions

* `TauCeti.ratToRealGL`: the change of scalars `GL(2, ℚ) →* GL(2, ℝ)`, the instance of `map` that
  the rational Hecke data is transported along to reach the group that acts on `ℍ`.

## Main results

* `Matrix.GeneralLinearGroup.map_injective`: entrywise application of an injective ring hom is
  injective on general linear groups.
* `TauCeti.ratToRealGL_injective`: that change of scalars is injective, so a subgroup of
  `GL(2, ℚ)` is carried isomorphically onto its image.
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

namespace TauCeti

/-- **The change of scalars from rational to real general linear groups.** `GL(2, ℚ)` does not act
on the upper half-plane; this is the entrywise map to `GL(2, ℝ)`, which does, and it is how every
statement relating rational matrix data to that action passes between the two. -/
noncomputable abbrev ratToRealGL : GL (Fin 2) ℚ →* GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-- **`ratToRealGL` is injective**, so a subgroup of `GL(2, ℚ)` is carried isomorphically onto its
image in `GL(2, ℝ)`. -/
theorem ratToRealGL_injective : Function.Injective ratToRealGL :=
  Matrix.GeneralLinearGroup.map_injective (algebraMap ℚ ℝ).injective

end TauCeti
