/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed submodules of commuting endomorphisms

This file supplements Mathlib's `LinearMap.fixedSubmodule`, the submodule of vectors fixed by a
linear endomorphism, with its invariance under commuting endomorphisms.

## Main results

* `TauCeti.apply_mem_fixedSubmodule_of_commute`: an endomorphism commuting with `g` maps the
  fixed submodule of `g` into itself.
-/

public section

namespace TauCeti

/-- An endomorphism commuting with `g` maps the fixed submodule of `g` into itself. -/
theorem apply_mem_fixedSubmodule_of_commute {R V : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] {f g : Module.End R V} (h : Commute g f) {x : V} (hx : x ∈ g.fixedSubmodule) :
    f x ∈ g.fixedSubmodule := by
  simpa [LinearMap.mem_fixedSubmodule_iff.1 hx] using LinearMap.congr_fun h.eq x

end TauCeti
