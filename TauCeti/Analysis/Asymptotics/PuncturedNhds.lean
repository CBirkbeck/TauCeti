/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Extending a big-`O` bound across the punctured point

A bound `f =O[𝓝[≠] a] g` says nothing at `a` itself, so it does not extend to `𝓝 a` in
general: if `g a = 0` while `f a ≠ 0`, no constant works there. Vanishing of `f` at the
point is exactly what closes that gap, and this file records the resulting extension.

Mathlib has the special case `g = 1` (`Asymptotics.isBigO_one_nhds_ne_iff`,
`Mathlib/Analysis/Asymptotics/Lemmas.lean:120`), stated as an `iff` and needing no hypothesis
at `a`, because there the bounding function is a nonzero constant. For a general `g` the
hypothesis is not removable, and only one direction survives.

## Main results

* `Asymptotics.IsBigO.of_puncturedNhds_of_norm_eq_zero`: a big-`O` bound on the punctured
  neighbourhood of `a` extends to the full neighbourhood, given `‖f a‖ = 0`.
-/

public section

open Filter Topology

namespace Asymptotics

variable {α E F : Type*} [TopologicalSpace α] [Norm E] [SeminormedAddCommGroup F]
  {f : α → E} {g : α → F} {a : α}

/-- **A big-`O` bound extends across the punctured point when `f` vanishes there.** The
constant supplied on `𝓝[≠] a` already works at `a` itself, since the left-hand side is `0`
there and the right-hand side is a nonnegative multiple of a norm.

The hypothesis `‖f a‖ = 0` cannot be dropped: with `g a = 0` and `f a ≠ 0` the conclusion
fails at `a` for every constant. -/
theorem IsBigO.of_puncturedNhds_of_norm_eq_zero (hO : f =O[𝓝[≠] a] g) (hf : ‖f a‖ = 0) :
    f =O[𝓝 a] g := by
  obtain ⟨C, hC0, hC⟩ := hO.exists_nonneg
  refine IsBigO.of_bound C ?_
  -- off `a` the punctured bound applies; at `a` both sides are pinned by `hf`
  have hpunct : ∀ᶠ x in 𝓝 a, x ≠ a → ‖f x‖ ≤ C * ‖g x‖ := by
    simpa [eventually_nhdsWithin_iff] using hC.bound
  filter_upwards [hpunct] with x hx
  by_cases hxa : x = a
  · subst hxa
    simpa [hf] using mul_nonneg hC0 (norm_nonneg _)
  · exact hx hxa

end Asymptotics

end
