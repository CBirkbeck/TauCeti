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

Wedhorn uses this in §7.1 to reduce to a MulArchimedean value group. It is *not* the §7.1.2
retraction `r_I`, which restricts a valuation into a convex subgroup — keeping the values whose
unit lies in `H` and sending the rest to `0` — rather than quotienting by it.

## Main definitions

* `TauCeti.ConvexSubgroup.coarsenMap` : The induced `MonoidWithZeroHom`
  `Γ₀ → WithZero (Γ₀ˣ ⧸ H)`.
* `Valuation.coarsen` : The valuation obtained by composing with `coarsenMap`.

## Main results

* `TauCeti.ConvexSubgroup.coarsenMap_monotone` : The coarsening map is monotone, which is
  what makes the composite a valuation.
* `TauCeti.ConvexSubgroup.coarsenMap_eq_one_iff` : `H` is exactly what the map forgets.
* `TauCeti.ConvexSubgroup.coarsenMap_lt_one_iff` : among nonzero values whose unit is already
  below `1`, coarsening stays strictly below `1` exactly for those `H` does not absorb.
  These are stated on `Γ₀`, not on a valuation: no valuation property enters, and the
  valuation-level forms follow from them by `simp` through `coarsen_apply`.
* `Valuation.coarsen_supp` : Coarsening does not change the support.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1

Ported from the AINTLIB development, `projects/AdicSpaces/Adic spaces/ValuationContinuity.lean`
(revision `fa3c5e6ee`, section "Coarsening to MulArchimedean value group"), adapted to the
pinned Mathlib: that development's `WithZero.mapMonoidWithZeroHom` is `WithZero.map'` here.
-/

public section

namespace TauCeti

namespace ConvexSubgroup

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The coarsening map `Γ₀ → WithZero (Γ₀ˣ ⧸ H)` attached to a convex subgroup `H` of `Γ₀ˣ`,
as the composite of the identification `Γ₀ ≃ WithZero Γ₀ˣ` with the quotient by `H`. -/
noncomputable def coarsenMap (H : ConvexSubgroup Γ₀ˣ) :
    Γ₀ →*₀ WithZero (Γ₀ˣ ⧸ H.toSubgroup) :=
  (WithZero.map' (QuotientGroup.mk' H.toSubgroup)).comp
    (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom

/-- The coarsening map is monotone. This is what lets it be composed with a valuation. -/
theorem coarsenMap_monotone (H : ConvexSubgroup Γ₀ˣ) : Monotone (coarsenMap H) := fun _ _ hab ↦
  WithZero.map'_mono (quotientMk_monotone H)
    ((OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toOrderIso.monotone hab)

/-- On a unit, the coarsening map is the quotient map. -/
@[simp]
theorem coarsenMap_coe_unit (H : ConvexSubgroup Γ₀ˣ) (g : Γ₀ˣ) :
    coarsenMap H (g : Γ₀) = ↑(QuotientGroup.mk' H.toSubgroup g) := by
  -- `OrderMonoidIso.withZeroUnits.symm.toMonoidWithZeroHom` and the bare `MulEquiv`
  -- `WithZero.withZeroUnitsEquiv.symm` are the same function definitionally; Mathlib has the
  -- lemma only for the latter, and no `@[simps]` projection bridges the two coercions.
  have h : (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom (g : Γ₀)
      = (g : WithZero Γ₀ˣ) :=
    WithZero.withZeroUnitsEquiv_symm_apply_coe g
  rw [coarsenMap, MonoidWithZeroHom.comp_apply, h, WithZero.map'_coe]

/-- The coarsening map sends a nonzero `x` to `1` exactly when `H` absorbs its unit. This is
the defining property of `H` as the subgroup being forgotten. -/
@[simp]
theorem coarsenMap_eq_one_iff (H : ConvexSubgroup Γ₀ˣ) {x : Γ₀} (hx : x ≠ 0) :
    coarsenMap H x = 1 ↔ Units.mk0 x hx ∈ H.toSubgroup := by
  have h : coarsenMap H x = ↑(QuotientGroup.mk' H.toSubgroup (Units.mk0 x hx)) :=
    coarsenMap_coe_unit H (Units.mk0 x hx)
  rw [h, ← WithZero.coe_one, WithZero.coe_inj, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]

/-- For a nonzero `x`, coarsening lands strictly below `1` exactly when the unit of `x` is
below `1` **and** `H` does not absorb it. Both conditions are needed: a unit at or above `1`
does not become smaller under coarsening, whatever `H` does. -/
@[simp]
theorem coarsenMap_lt_one_iff (H : ConvexSubgroup Γ₀ˣ) {x : Γ₀} (hx : x ≠ 0) :
    coarsenMap H x < 1 ↔ Units.mk0 x hx < 1 ∧ Units.mk0 x hx ∉ H.toSubgroup := by
  have h : coarsenMap H x = ↑(QuotientGroup.mk' H.toSubgroup (Units.mk0 x hx)) :=
    coarsenMap_coe_unit H (Units.mk0 x hx)
  rw [h, ← WithZero.coe_one, WithZero.coe_lt_coe, QuotientGroup.mk'_apply]
  exact quotientMk_lt_one_iff H

end ConvexSubgroup

end TauCeti

namespace Valuation

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {R : Type*} [Ring R]

/-- The **coarsening** of a valuation by a convex subgroup `H` of the units of its value
monoid: the composite of `v` with `TauCeti.ConvexSubgroup.coarsenMap H`. -/
noncomputable def coarsen (v : Valuation R Γ₀) (H : TauCeti.ConvexSubgroup Γ₀ˣ) :
    Valuation R (WithZero (Γ₀ˣ ⧸ H.toSubgroup)) :=
  v.map H.coarsenMap H.coarsenMap_monotone

@[simp]
theorem coarsen_apply (v : Valuation R Γ₀) (H : TauCeti.ConvexSubgroup Γ₀ˣ) (r : R) :
    v.coarsen H r = H.coarsenMap (v r) :=
  Valuation.map_apply _ _ _ _

/-- Coarsening leaves the support unchanged: the coarsening map kills only `0`. -/
@[simp]
theorem coarsen_supp {R : Type*} [CommRing R] (v : Valuation R Γ₀)
    (H : TauCeti.ConvexSubgroup Γ₀ˣ) : (v.coarsen H).supp = v.supp := by
  ext r
  simp [mem_supp_iff]

end Valuation
