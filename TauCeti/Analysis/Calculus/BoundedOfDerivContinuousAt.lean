/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Boundedness near an endpoint from a continuous derivative

A complex function whose derivative along the real interval `(a, ∞)` is the restriction of a
function continuous at `a` stays bounded along the reals as the variable tends to `a` from the
right. The derivative is bounded on a short interval `(a, a + ε)`, so the mean value inequality
bounds the function there.

## Main results

* `TauCeti.exists_norm_le_of_hasDerivAt_of_continuousAt`: if `f' = g` on `(a, ∞) ⊆ ℝ` and `g` is
  continuous at `a`, then `‖f t‖` is eventually bounded as `t → a⁺`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- **Boundedness near `a⁺` from a derivative continuous at `a`.** If `f : ℂ → ℂ` has derivative
`g u` at every real `u > a` and `g` is continuous at `a`, then `‖f t‖` is eventually bounded as
the real variable `t` tends to `a` from the right. -/
theorem exists_norm_le_of_hasDerivAt_of_continuousAt {f g : ℂ → ℂ} {a : ℝ}
    (hg : ContinuousAt g a) (hf : ∀ u : ℝ, a < u → HasDerivAt f (g u) u) :
    ∃ B, ∀ᶠ t : ℝ in 𝓝[>] a, ‖f t‖ ≤ B := by
  -- `‖g‖ < ‖g a‖ + 1` near `a`, so `f` is Lipschitz along the reals there.
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hg.comp Complex.continuous_ofReal.continuousAt).norm.eventually_lt continuousAt_const
      (lt_add_one ‖g a‖))
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ ∈ Set.Ioo a (a + ε) := ⟨a + ε / 2, by linarith, by linarith⟩
  refine ⟨‖f x₀‖ + (‖g a‖ + 1) * ε, ?_⟩
  have haε : a < a + ε := lt_add_of_pos_right a hε
  filter_upwards [Ioo_mem_nhdsGT haε] with t ht
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ ↦ f u) (f' := fun u : ℝ ↦ g u)
    (fun u hu ↦ ((hf u hu.1).comp_ofReal).hasDerivWithinAt)
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
