/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Boundedness near an endpoint from a continuous derivative

A function on the reals whose derivative just to the right of `a` is given by a function
continuous at `a` stays bounded as the variable tends to `a` from the right. The derivative is
bounded on a short interval `(a, a + ε)`, so the mean value inequality bounds the function there.

## Main results

* `TauCeti.exists_norm_le_of_hasDerivAt_of_continuousAt`: if `f' = g` on a right neighbourhood
  of `a` and `g` is continuous at `a`, then `‖f t‖` is eventually bounded as `t → a⁺`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- **Boundedness near `a⁺` from a derivative continuous at `a`.** If `f : ℝ → E` has derivative
`g u` at every `u` in a right neighbourhood of `a` and `g` is continuous at `a`, then `‖f t‖` is
eventually bounded as `t` tends to `a` from the right. -/
theorem exists_norm_le_of_hasDerivAt_of_continuousAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : ℝ → E} {a : ℝ} (hg : ContinuousAt g a)
    (hf : ∀ᶠ u in 𝓝[>] a, HasDerivAt f (g u) u) :
    ∃ B, ∀ᶠ t in 𝓝[>] a, ‖f t‖ ≤ B := by
  -- `‖g‖ < ‖g a‖ + 1` near `a`, and `f' = g` on some `(a, a + δ)`: so `f` is Lipschitz on
  -- `(a, a + ε)` for `ε ≤ δ` small.
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.mp
    (hg.norm.eventually_lt continuousAt_const (lt_add_one ‖g a‖))
  obtain ⟨b, hb, hfb⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hf
  set ε := min ε₁ (b - a)
  have hε : 0 < ε := lt_min hε₁ (sub_pos.mpr hb)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ ∈ Set.Ioo a (a + ε) := ⟨a + ε / 2, by linarith, by linarith⟩
  refine ⟨‖f x₀‖ + (‖g a‖ + 1) * ε, ?_⟩
  have haε : a < a + ε := lt_add_of_pos_right a hε
  have hεb : a + ε ≤ b := by linarith [min_le_right ε₁ (b - a)]
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  filter_upwards [Ioo_mem_nhdsGT haε] with t ht
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := g)
    (fun u hu ↦ (hfb ⟨hu.1, hu.2.trans_le hεb⟩).hasDerivWithinAt)
    (fun u hu ↦ (hball (by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2])).le) (convex_Ioo _ _) hx₀ ht
  have hdist : ‖t - x₀‖ ≤ ε := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2, hx₀.1, hx₀.2]
  calc ‖f t‖ ≤ ‖f x₀‖ + ‖f t - f x₀‖ := norm_le_insert' _ _
    _ ≤ ‖f x₀‖ + (‖g a‖ + 1) * ε := by
        gcongr
        exact hmvt.trans (by gcongr)

end TauCeti
