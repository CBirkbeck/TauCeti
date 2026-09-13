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

/-- **A punctured `O`-bound extends across the puncture** when the comparator cannot vanish
alone there: if `f =O[𝓝[≠] a] g` and `‖g a‖ = 0 → ‖f a‖ = 0`, then `f =O[𝓝 a] g`.

The hypothesis constrains only the puncture, and only where it must. Where `‖g a‖ = 0` the bound
at `a` reads `‖f a‖ ≤ C * 0`, so `‖f a‖ = 0` is exactly what is needed and exactly what is
assumed; where `‖g a‖ ≠ 0` nothing is needed, since enlarging the constant covers a single point.

Stated with norms rather than `g a = 0 → f a = 0` because the codomains are only *semi*normed:
there `g a ≠ 0` does not give `‖g a‖ > 0`, and the version with points is not enough to bound
`f a`. -/
theorem isBigO_nhds_of_isBigO_punctured {α : Type*} [TopologicalSpace α] {a : α}
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {f : α → E} {g : α → F}
    (hO : f =O[𝓝[≠] a] g) (hf : ‖g a‖ = 0 → ‖f a‖ = 0) : f =O[𝓝 a] g := by
  obtain ⟨C, hC0, hC⟩ := hO.exists_nonneg
  have hC' : ∀ᶠ x : α in 𝓝 a, x ≠ a → ‖f x‖ ≤ C * ‖g x‖ := by
    simpa [eventually_nhdsWithin_iff] using hC.bound
  rcases eq_or_lt_of_le (norm_nonneg (g a)) with hga | hga
  · refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hC'] with x hx
    by_cases hxa : x = a
    · subst hxa
      simp [hf hga.symm, ← hga]
    · exact hx hxa
  · refine Asymptotics.IsBigO.of_bound (max C (‖f a‖ / ‖g a‖)) ?_
    filter_upwards [hC'] with x hx
    by_cases hxa : x = a
    · subst hxa
      exact (div_le_iff₀ hga).1 (le_max_right _ _)
    · exact (hx hxa).trans (by gcongr; exact le_max_left _ _)

end TauCeti
