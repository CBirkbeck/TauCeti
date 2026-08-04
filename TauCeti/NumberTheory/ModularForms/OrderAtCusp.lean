/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.QExpansion.Order

/-!
# The vanishing order at the cusp

The vanishing order of a modular form at the cusp is the order of its `q`-expansion, as an
integer with junk value `0` at the identically vanishing expansion — the convention of the
interior dictionary `orderOfVanishingAt`. For a modular form it is computed by the analytic
order of the cusp function at `0`, vanishes when the constant term is nonzero, and rescales
linearly in the width — the cusp term of the valence formula.

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

open scoped ModularForm

namespace TauCeti

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {f : F} {h : ℝ}

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

/-- The cusp order of a modular form is the analytic order of its cusp function at `0`. -/
lemma orderAtCusp_eq_analyticOrderAt [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) :
    orderAtCusp h f = ((analyticOrderAt (cuspFunction h f) 0).toNat : ℤ) := by
  rw [orderAtCusp_def, qExpansion_order_eq_analyticOrderAt_cuspFunction
    (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)]

/-- A modular form whose constant term at the cusp is nonzero has cusp order zero. -/
lemma orderAtCusp_eq_zero_of_cuspFunction_ne_zero [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (h0 : cuspFunction h f 0 ≠ 0) : orderAtCusp h f = 0 := by
  rw [orderAtCusp_eq_analyticOrderAt hh hΓ,
    (ModularFormClass.analyticAt_cuspFunction_zero f hh
      hΓ).analyticOrderAt_eq_zero.mpr h0]
  rfl

/-- The cusp order rescales linearly in the width. -/
lemma orderAtCusp_nat_mul [ModularFormClass F Γ k] {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hΓ : h ∈ Γ.strictPeriods) :
    orderAtCusp (m * h) f = m * orderAtCusp h f := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  rw [orderAtCusp_def, orderAtCusp_def,
    qExpansion_nat_mul_order hh hm (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.bdd_at_infty f) (ModularFormClass.holo f),
    ENat.toNat_mul]
  simp [mul_comm]

end ModularForm

end TauCeti

end
