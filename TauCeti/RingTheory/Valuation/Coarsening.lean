/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Algebra.Order.Group.ConvexSubgroup

/-!
# Coarsening a valuation by a convex subgroup

A convex subgroup `H` of the units `Γ₀ˣ` of a value monoid is exactly the kernel of an
order-compatible quotient of `Γ₀ˣ`, so composing a valuation with that quotient yields another
valuation — its **coarsening** by `H`. Coarsening forgets the part of the value group lying
inside `H` while keeping the order relation between the remaining classes.

This is the construction behind the retraction `r_I : Spv A → Spv (A, I)` of Wedhorn §7.1.2,
which coarsens `v` by the ideal-indexed characteristic subgroup `cΓ_v(I)`.

## Main definitions

* `TauCeti.coarsenMap` : The induced `MonoidWithZeroHom` `Γ₀ → WithZero (Γ₀ˣ ⧸ H)`.
* `Valuation.coarsen` : The valuation obtained by composing with `coarsenMap`.

## Main results

* `TauCeti.coarsenMap_monotone` : The coarsening map is monotone, which is what makes the
  composite a valuation.
* `Valuation.coarsen_supp` : Coarsening does not change the support.
* `Valuation.coarsen_le_one_of_le_one` and `Valuation.coarsen_lt_one_of_notMem` : how the
  bounds `≤ 1` and `< 1` transport, the second being the reason `r_I` lands where it does.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1

Ported from the AINTLIB development, `projects/AdicSpaces/Adic spaces/ValuationContinuity.lean`
(revision `fa3c5e6ee`, section "Coarsening to MulArchimedean value group"), adapted to the
pinned Mathlib: that development's `WithZero.mapMonoidWithZeroHom` is `WithZero.map'` here.
-/

public section

namespace TauCeti

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The coarsening map `Γ₀ → WithZero (Γ₀ˣ ⧸ H)` attached to a convex subgroup `H` of `Γ₀ˣ`,
as the composite of the identification `Γ₀ ≃ WithZero Γ₀ˣ` with the quotient by `H`. -/
noncomputable def coarsenMap (H : ConvexSubgroup Γ₀ˣ) :
    Γ₀ →*₀ WithZero (Γ₀ˣ ⧸ H.toSubgroup) :=
  (WithZero.map' (QuotientGroup.mk' H.toSubgroup)).comp
    (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom

/-- The coarsening map is monotone. This is what lets it be composed with a valuation. -/
theorem coarsenMap_monotone (H : ConvexSubgroup Γ₀ˣ) : Monotone (coarsenMap H) := fun _ _ hab ↦
  WithZero.map'_mono (ConvexSubgroup.quotientMk_monotone H)
    ((OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toOrderIso.monotone hab)

/-- On a unit, the coarsening map is the quotient map. -/
@[simp]
theorem coarsenMap_coe_unit (H : ConvexSubgroup Γ₀ˣ) (g : Γ₀ˣ) :
    coarsenMap H (g : Γ₀) = ↑(QuotientGroup.mk' H.toSubgroup g) := by
  have h : (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom (g : Γ₀)
      = (g : WithZero Γ₀ˣ) :=
    WithZero.withZeroUnitsEquiv_symm_apply_coe g
  rw [coarsenMap, MonoidWithZeroHom.comp_apply, h, WithZero.map'_coe]

end TauCeti

namespace Valuation

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {R : Type*} [Ring R]

/-- The **coarsening** of a valuation by a convex subgroup `H` of the units of its value
monoid: the composite of `v` with `TauCeti.coarsenMap H`. -/
noncomputable def coarsen (v : Valuation R Γ₀) (H : TauCeti.ConvexSubgroup Γ₀ˣ) :
    Valuation R (WithZero (Γ₀ˣ ⧸ H.toSubgroup)) :=
  v.map (TauCeti.coarsenMap H) (TauCeti.coarsenMap_monotone H)

@[simp]
theorem coarsen_apply (v : Valuation R Γ₀) (H : TauCeti.ConvexSubgroup Γ₀ˣ) (r : R) :
    v.coarsen H r = TauCeti.coarsenMap H (v r) :=
  Valuation.map_apply _ _ _ _

/-- Coarsening preserves the bound `v a ≤ 1`. -/
theorem coarsen_le_one_of_le_one (v : Valuation R Γ₀) (H : TauCeti.ConvexSubgroup Γ₀ˣ)
    {a : R} (ha : v a ≤ 1) : v.coarsen H a ≤ 1 := by
  simpa using TauCeti.coarsenMap_monotone H ha

/-- A nonzero value `≤ 1` whose unit avoids `H` becomes *strictly* less than `1` after
coarsening. This is what makes the retraction of Wedhorn §7.1.2 land where it does: the values
that survive as `< 1` are exactly those the convex subgroup does not absorb. -/
theorem coarsen_lt_one_of_notMem (v : Valuation R Γ₀) (H : TauCeti.ConvexSubgroup Γ₀ˣ)
    {a : R} (ha : v a ≠ 0) (hnot : Units.mk0 (v a) ha ∉ H) (hle : v a ≤ 1) :
    v.coarsen H a < 1 := by
  have hlt : Units.mk0 (v a) ha < 1 := lt_of_le_of_ne (Units.val_le_val.mp hle)
    fun h ↦ hnot (h ▸ one_mem H)
  rw [coarsen_apply, show v a = ((Units.mk0 (v a) ha : Γ₀ˣ) : Γ₀) from rfl,
    TauCeti.coarsenMap_coe_unit]
  exact WithZero.coe_lt_one.mpr (TauCeti.ConvexSubgroup.quotientMk_lt_one_of_notMem H hlt hnot)

/-- Coarsening leaves the support unchanged: the coarsening map kills only `0`. -/
@[simp]
theorem coarsen_supp {R : Type*} [CommRing R] (v : Valuation R Γ₀)
    (H : TauCeti.ConvexSubgroup Γ₀ˣ) : (v.coarsen H).supp = v.supp := by
  ext r
  simp [mem_supp_iff]

end Valuation
