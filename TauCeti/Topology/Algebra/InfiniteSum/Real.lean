/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Weighted geometric majorants over an index and an exponent

For a family `r : ι → E` in a normed group, all of norm less than one and eventually of norm at
most `1 - ε`, the double family `(i, e) ↦ w i * ‖r i‖ ^ (e + 1)` is summable over `ι × ℕ` as soon
as `i ↦ w i * ‖r i‖` is summable. Each fibre is geometric, so it sums to
`w i * ‖r i‖ / (1 - ‖r i‖)`, and the eventual bound keeps `1 / (1 - ‖r i‖)` under `ε⁻¹` off a
finite set.

## Main results

* `TauCeti.summable_mul_norm_pow_succ`: the weighted double family is summable over `ι × ℕ`.
-/

public section

namespace TauCeti

/-- **A weighted geometric family is summable over index and exponent together.**  For a family
`r` in a normed group, all of norm less than one and eventually of norm at most `1 - ε`, and real
weights `w` with `i ↦ w i * ‖r i‖` summable, the double family `(i, e) ↦ w i * ‖r i‖ ^ (e + 1)` is
summable over `ι × ℕ`.

The weights are unrestricted in sign: only `|w i|` enters the majorant. The eventual bound is what
the fibres need — the fibre at `i` sums to `w i * ‖r i‖ / (1 - ‖r i‖)`, which is comparable to
`w i * ‖r i‖` only where `‖r i‖` stays away from `1`. Summability of `r` would give this, but is
far stronger: it rules out a family of constant norm with summable weights.

This is the bound a termwise differentiation argument runs on whenever the differentiated terms are
an index-only weight times a norm power; it says nothing on its own about which families have that
form. -/
theorem summable_mul_norm_pow_succ {ι E : Type*} [NormedAddCommGroup E] {r : ι → E} {w : ι → ℝ}
    (hbd : ∃ ε > 0, ∀ᶠ i in Filter.cofinite, ‖r i‖ ≤ 1 - ε)
    (hwr : Summable fun i ↦ w i * ‖r i‖) (h1 : ∀ i, ‖r i‖ < 1) :
    Summable fun ie : ι × ℕ ↦ w ie.1 * ‖r ie.1‖ ^ (ie.2 + 1) := by
  obtain ⟨ε, hε, hfar⟩ := hbd
  have habs : Summable fun i ↦ |w i| * ‖r i‖ := by
    refine (summable_abs_iff.2 hwr).congr fun i ↦ ?_
    rw [abs_mul, abs_of_nonneg (norm_nonneg (r i))]
  -- The absolute-value family is nonnegative, so it can be assembled fibrewise.
  have hfib : ∀ i, Summable fun e : ℕ ↦ |w i| * ‖r i‖ ^ (e + 1) := fun i ↦
    (((summable_geometric_of_lt_one (norm_nonneg _) (h1 i)).mul_left ‖r i‖).congr
      fun e ↦ by ring).mul_left |w i|
  have hval : ∀ i, ∑' e : ℕ, |w i| * ‖r i‖ ^ (e + 1) = |w i| * (‖r i‖ / (1 - ‖r i‖)) := fun i ↦ by
    rw [tsum_mul_left, tsum_congr fun e ↦ pow_succ' ‖r i‖ e, tsum_mul_left,
      tsum_geometric_of_lt_one (norm_nonneg _) (h1 i), div_eq_mul_inv]
  have houter : Summable fun i ↦ ∑' e : ℕ, |w i| * ‖r i‖ ^ (e + 1) := by
    refine Summable.of_norm_bounded_eventually (g := fun i ↦ ε⁻¹ * (|w i| * ‖r i‖))
      (habs.mul_left ε⁻¹) ?_
    filter_upwards [hfar] with i hi
    rw [Real.norm_of_nonneg (tsum_nonneg fun e ↦ by positivity), hval i]
    -- Where `‖r i‖ ≤ 1 - ε` the fibre sum `‖r i‖ / (1 - ‖r i‖)` is at most `ε⁻¹ ‖r i‖`.
    have hd : ‖r i‖ / (1 - ‖r i‖) ≤ ε⁻¹ * ‖r i‖ := by
      rw [div_le_iff₀ (by linarith [h1 i])]
      have hεi : ε * (ε⁻¹ * ‖r i‖) = ‖r i‖ := by field_simp
      nlinarith [norm_nonneg (r i), inv_pos.2 hε]
    calc |w i| * (‖r i‖ / (1 - ‖r i‖)) ≤ |w i| * (ε⁻¹ * ‖r i‖) :=
          mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = ε⁻¹ * (|w i| * ‖r i‖) := by ring
  have hmaj : Summable fun ie : ι × ℕ ↦ |w ie.1| * ‖r ie.1‖ ^ (ie.2 + 1) :=
    (summable_prod_of_nonneg fun ie ↦ by positivity).mpr ⟨hfib, houter⟩
  refine hmaj.of_norm_bounded fun ie ↦ ?_
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖r ie.1‖ ^ (ie.2 + 1))]

end TauCeti
