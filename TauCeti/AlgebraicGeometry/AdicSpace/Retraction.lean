/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.SpvOfIdeal
public import TauCeti.RingTheory.Valuation.RestrictToConvex

/-!
# The retraction `r_I : Spv A → Spv (A, I)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §7.1.2.**

A valuation is sent to its restriction to `cΓ_v(I)`: values whose unit lies in that convex
subgroup are kept, and every other value is sent to `0`. The result lands in `Spv (A, I)`, and a
point already there is fixed, so this is a retraction of `Spv A` onto the subspace.

## Main definitions

* `TauCeti.Valuation.restrictToIdeal` : the restricted valuation `v|cΓ_v(I)`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1.2

The construction is the one AINTLIB calls `restrictIdeal`
(`aintlib-adic-spaces`, `projects/AdicSpaces/Adic spaces/CharacteristicSubgroup.lean`), built on
`restrictToConvexBounded`; the general restriction lives in
`TauCeti.RingTheory.Valuation.RestrictToConvex`. TauCeti's `cΓ_v(I)` is a convex subgroup of the
*value group*, so it is transported onto the units of the value monoid before being restricted
to — AINTLIB's `cGammaIdeal` is already phrased on `Γ₀ˣ` and needs no such step.
-/

public section

namespace TauCeti.Valuation

open MonoidWithZeroHom TauCeti

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The units identification takes the unit of a restricted value to the value-group element it
names. This is the bridge between membership in a transported convex subgroup, which is phrased
through `OrderMonoidIso.unitsWithZero`, and the introduction rules for `cΓ_v(I)`, which are
phrased through `valueGroup.mk`. -/
private theorem unitsWithZeroEquiv_mk0_restrict (v : Valuation A Γ₀) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0) (ha : v.restrict a ≠ 0) :
    OrderMonoidIso.unitsWithZero (Units.mk0 (v.restrict a) ha) =
      valueGroup.mk (.ofClass v) 1 a (by simp) h0 := by
  rw [← WithZero.coe_inj, ← v.restrict_eq_mk h0]
  exact WithZero.coe_unitsWithZeroEquiv_eq_units_val _

/-- `cΓ_v(I)`, transported onto the units of the value monoid, absorbs every attained value
`≥ 1`. This is exactly the hypothesis `Valuation.restrictToConvex` needs, and it holds because
`cΓ_v(I)` contains `cΓ_v`, which contains every attained value `≥ 1`. -/
theorem mk0_restrict_mem_ofValueGroup (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (a : A) (ha : v.restrict a ≠ 0) (h1 : 1 ≤ v.restrict a) :
    Units.mk0 (v.restrict a) ha ∈
      ConvexSubgroup.ofValueGroup (characteristicSubgroupOfIdeal v I hfg) := by
  have h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := fun h => ha (v.restrict_eq_zero_iff.mpr h)
  rw [mem_convexSubgroup_ofValueGroup, unitsWithZeroEquiv_mk0_restrict v h0 ha]
  refine characteristicSubgroup_le_characteristicSubgroupOfIdeal v I hfg
    (valueGroup_mk_mem_characteristicSubgroup_of_one_le_value h0 ?_)
  have hr : v.restrict 1 ≤ v.restrict a := by simpa using h1
  simpa using v.restrict_le_iff.mp hr

/-- **Wedhorn §7.1.2: the restriction `v ↦ v|cΓ_v(I)`.** Values whose unit lies in `cΓ_v(I)` are
kept; every other value is sent to `0`. -/
noncomputable def restrictToIdeal (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    Valuation A (WithZero
      (ConvexSubgroup.ofValueGroup (characteristicSubgroupOfIdeal v I hfg)).toSubgroup) :=
  (v.restrict).restrictToConvex _ (mk0_restrict_mem_ofValueGroup v I hfg)

end TauCeti.Valuation

namespace TauCeti.ValuationSpectrum

open MonoidWithZeroHom TauCeti TauCeti.Valuation

variable {A : Type*} [CommRing A]

/-- **The underlying map of Wedhorn's §7.1.2 retraction.** A point of `Spv A` is sent to the
class of its canonical valuation restricted to `cΓ_v(I)`.

The `letI` is load-bearing. `Valuation` asks only for `LinearOrderedCommMonoidWithZero`, so the
restriction's codomain elaborates with `WithZero`'s direct monoid instance, while `ofValuation`
wants the group class; the two paths agree by `rfl` but not reducibly, so unification needs the
instance pinned. -/
noncomputable def retract (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) : Spv A :=
  letI : LinearOrderedCommGroupWithZero (WithZero (ConvexSubgroup.ofValueGroup
      (characteristicSubgroupOfIdeal v.valuation I hfg)).toSubgroup) := inferInstance
  ofValuation (v.valuation.restrictToIdeal I hfg)

end TauCeti.ValuationSpectrum
