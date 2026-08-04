/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.QExpansion.Order

/-!
# The vanishing order at the cusp

The vanishing order of a modular form at the cusp is the order of its `q`-expansion, as an
integer with junk value `0` at the identically vanishing expansion — the convention of the
interior dictionary `orderOfVanishingAt`. It is computed by the analytic order of the cusp
function at `0`, vanishes when the constant term is nonzero, and rescales linearly in the
width — the cusp term of the valence formula. The lemmas take the raw analytic, periodicity,
and boundedness hypotheses of the underlying `q`-expansion theorems; for a modular form all
of them are supplied by the `ModularFormClass` machinery.

## Main declarations

* `TauCeti.ModularForm.orderAtCusp`.
* `TauCeti.ModularForm.orderAtCusp_eq_analyticOrderAt`: the analytic-order dictionary.
* `TauCeti.ModularForm.orderAtCusp_nat_mul`: linear rescaling in the width.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex Function SlashInvariantForm Periodic

open scoped ModularForm Topology Filter Manifold

namespace TauCeti

namespace ModularForm

variable {h : ℝ} {g : ℍ → ℂ}

/-- The vanishing order at the cusp: the order of the `q`-expansion at width `h`, as an
integer, with junk value `0` when the expansion vanishes identically — the `untop₀`
convention of `orderOfVanishingAt`. -/
def orderAtCusp (h : ℝ) (f : ℍ → ℂ) : ℤ := ((qExpansion h f).order.toNat : ℤ)

/-- `orderAtCusp` unfolded to the `q`-expansion order. The definition is sealed by the
module system; this equation is the supported cross-module rewrite. -/
lemma orderAtCusp_def (h : ℝ) (f : ℍ → ℂ) :
    orderAtCusp h f = ((qExpansion h f).order.toNat : ℤ) := by
  unfold orderAtCusp
  rfl

/-- The cusp order is nonnegative. -/
lemma orderAtCusp_nonneg (h : ℝ) (f : ℍ → ℂ) : 0 ≤ orderAtCusp h f := by
  rw [orderAtCusp_def]
  exact Int.natCast_nonneg _

/-- The cusp order is the analytic order of the cusp function at `0`. For a modular form
the analyticity is `ModularFormClass.analyticAt_cuspFunction_zero`. -/
lemma orderAtCusp_eq_analyticOrderAt (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    orderAtCusp h g = ((analyticOrderAt (cuspFunction h g) 0).toNat : ℤ) := by
  rw [orderAtCusp_def, qExpansion_order_eq_analyticOrderAt_cuspFunction hg]

/-- A nonzero constant term at the cusp forces cusp order zero. -/
lemma orderAtCusp_eq_zero_of_cuspFunction_ne_zero (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (h0 : cuspFunction h g 0 ≠ 0) : orderAtCusp h g = 0 := by
  rw [orderAtCusp_eq_analyticOrderAt hg, hg.analyticOrderAt_eq_zero.mpr h0]
  rfl

/-- The cusp order rescales linearly in the width. For a modular form the periodicity,
boundedness, and holomorphy are `SlashInvariantFormClass.periodic_comp_ofComplex`,
`ModularFormClass.bdd_at_infty`, and `ModularFormClass.holo`. -/
lemma orderAtCusp_nat_mul {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg_bdd : IsBoundedAtImInfty g)
    (hg_mdiff : MDiff g) : orderAtCusp (m * h) g = m * orderAtCusp h g := by
  rw [orderAtCusp_def, orderAtCusp_def,
    qExpansion_nat_mul_order hh hm hg_per hg_bdd hg_mdiff, ENat.toNat_mul]
  simp [mul_comm]

end ModularForm

end TauCeti

end
