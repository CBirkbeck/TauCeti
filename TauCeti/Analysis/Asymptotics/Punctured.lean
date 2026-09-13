/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Basic

/-!
# Extending an `O`-bound across a puncture

A bound `f =O[𝓝[≠] a] g` says nothing about `f` at `a` itself. If `f` vanishes there, the bound
extends to the full neighbourhood for free: the inequality `‖f a‖ ≤ C * ‖g a‖` holds because its
left side is `0` and its right side is a nonnegative multiple of a norm.

## Main results

* `TauCeti.isBigO_nhds_of_isBigO_punctured`: a punctured `O`-bound at a point where the
  bounded function vanishes is an `O`-bound on the whole neighbourhood.
-/

public section

namespace TauCeti

open Filter Topology

/-- **A punctured `O`-bound extends across the puncture** when the bounded function vanishes
there: if `f =O[𝓝[≠] a] g` and `f a = 0`, then `f =O[𝓝 a] g`.

Only the value of `f` at `a` is constrained; `g a` is arbitrary, since the bound at `a` reads
`0 ≤ C * ‖g a‖`, which holds for any nonnegative `C`. -/
theorem isBigO_nhds_of_isBigO_punctured {α : Type*} [TopologicalSpace α] {a : α}
    {E F : Type*} [NormedAddCommGroup E] [SeminormedAddCommGroup F] {f : α → E} {g : α → F}
    (hO : f =O[𝓝[≠] a] g) (hf : f a = 0) : f =O[𝓝 a] g := by
  obtain ⟨C, hC0, hC⟩ := hO.exists_nonneg
  refine Asymptotics.IsBigO.of_bound C ?_
  have hC' : ∀ᶠ x : α in 𝓝 a, x ≠ a → ‖f x‖ ≤ C * ‖g x‖ := by
    simpa [eventually_nhdsWithin_iff] using hC.bound
  filter_upwards [hC'] with x hx
  by_cases hxa : x = a
  · subst hxa
    simpa [hf] using mul_nonneg hC0 (norm_nonneg (g x))
  · exact hx hxa

end TauCeti
