/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bounds that hold up to a vanishing correction

Mathlib's `ge_of_tendsto` passes an eventual bound to a limit.  A common way to meet its hypothesis
is to prove the bound only up to a correction that dies away, which this file packages.

## Main results

* `le_of_eventually_le_add_mul_of_tendsto_zero`: if `v ≤ K + g B * m` eventually and `g B → 0`,
  then `v ≤ K`.
-/

public section

open Filter Topology

/-- **A bound holding up to a vanishing correction holds outright.**  If `v ≤ K + g B * m` for all
large `B`, and `g B` tends to `0`, then `v ≤ K`.

No sign condition on `v`, `K` or `m` is required. -/
theorem le_of_eventually_le_add_mul_of_tendsto_zero {v K m : ℝ} {g : ℝ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) (h : ∀ᶠ B in atTop, v ≤ K + g B * m) : v ≤ K :=
  ge_of_tendsto (by simpa using tendsto_const_nhds.add (hg.mul_const m)) h
