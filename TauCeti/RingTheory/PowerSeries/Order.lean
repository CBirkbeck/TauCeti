/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Self-multiplication cancellation for formal power series

A formal power series fixed by multiplication with a series of zero constant coefficient is zero:
if `f = g * f` in `R⟦X⟧` and `constantCoeff g = 0`, then `f = 0`.

The mechanism is the order valuation. Zero constant coefficient means `1 ≤ order g`, and
`order g + order f ≤ order (g * f)`, so the hypothesis gives `order f + 1 ≤ order f`. In `ℕ∞`
that forces `order f = ⊤`, which is to say `f = 0`.

This is the uniqueness engine for recursively defined power series: two solutions of the same
recurrence have a difference `f` satisfying exactly such a fixed-point equation, with the `g`
coming from the recurrence and having no constant term.

## Main results

* `PowerSeries.eq_zero_of_self_eq_mul_self`: `constantCoeff g = 0` and `f = g * f` give `f = 0`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/PowerSeriesHelpers.lean`, declaration `eq_zero_of_self_eq_mul_self`. The source's
companion `eq_zero_of_self_eq_self_mul` — the `f = f * g` form over a `CommSemiring` — is not
ported: it is `mul_comm` away, and is better written at a call site than carried as API.
-/

public section

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- **Self-multiplication cancellation.** If `f = g * f` in `R⟦X⟧` and `g` has zero constant
coefficient, then `f = 0`.

Over a `CommSemiring` the `f = f * g` form follows by `mul_comm`. -/
theorem eq_zero_of_self_eq_mul_self {f g : R⟦X⟧} (hg : constantCoeff g = 0) (h : f = g * f) :
    f = 0 := by
  by_contra hf
  -- `order g ≥ 1`, so the order of `g * f` strictly exceeds that of `f` unless `f = 0`.
  have hgorder : (1 : ℕ∞) ≤ g.order := one_le_order_iff_constCoeff_eq_zero.mpr hg
  have habsurd : f.order + 1 ≤ f.order :=
    calc f.order + 1 = 1 + f.order := by rw [add_comm]
      _ ≤ g.order + f.order := by gcongr
      _ ≤ (g * f).order := le_order_mul g f
      _ = f.order := (congrArg _ h).symm
  exact absurd ((ENat.add_one_le_iff <| order_eq_top.not.mpr hf).mp habsurd) (lt_irrefl _)

end PowerSeries
