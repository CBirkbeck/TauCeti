/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Valuation.CofinalIdeal.Greatest
public import TauCeti.RingTheory.Valuation.RestrictToConvex

/-!
# Restricting a valuation to `cΓ_v(I)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §7.1.2.**

`Valuation.restrictToConvex` restricts a valuation to an arbitrary convex subgroup of the units
of its value monoid. This file specialises it to the convex subgroup that matters for
`Spv (A, I)`: the characteristic subgroup `cΓ_v(I)` of an ideal, from Wedhorn's Definition 7.3.

Two things have to be arranged. `cΓ_v(I)` lives in the value *group*, so it is transported onto
the units of the value monoid by `ConvexSubgroup.comapUnitsWithZero`; and the restriction needs
`cΓ_v(I)` to absorb every attained value `≥ 1`, which holds because it contains `cΓ_v`.

The point-level map on `Spv A` that Wedhorn's retraction `r_I` is built from lives in
`TauCeti.AlgebraicGeometry.AdicSpace.Retraction`.

## Main definitions

* `TauCeti.Valuation.RestrictedValues` : the value monoid the restriction lands in.
* `TauCeti.Valuation.restrictToIdeal` : the restricted valuation `v|cΓ_v(I)`.

## Main results

* `TauCeti.Valuation.mk0_restrict_mem_comapUnitsWithZero_iff` : membership in the transported
  `cΓ_v(I)`, converted to membership in `cΓ_v(I)` itself — the form consumers hold.
* `TauCeti.Valuation.restrictToIdeal_apply_of_mem`,
  `TauCeti.Valuation.restrictToIdeal_apply_of_notMem`,
  `TauCeti.Valuation.restrictToIdeal_apply_of_eq_zero` : the three branches.
* `TauCeti.Valuation.restrictToIdeal_eq_zero_iff` : where the restriction vanishes, totally.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1.2

The construction is the one AINTLIB calls `restrictIdeal`
(`aintlib-adic-spaces`, `projects/AdicSpaces/Adic spaces/CharacteristicSubgroup.lean`), built on
`restrictToConvexBounded`. AINTLIB's `cGammaIdeal` is already phrased on `Γ₀ˣ` and so needs no
transport.
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
private theorem mk0_restrict_mem_comapUnitsWithZero (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (a : A) (ha : v.restrict a ≠ 0) (h1 : 1 ≤ v.restrict a) :
    Units.mk0 (v.restrict a) ha ∈
      ConvexSubgroup.comapUnitsWithZero (characteristicSubgroupOfIdeal v I hfg) := by
  have h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := fun h => ha (v.restrict_eq_zero_iff.mpr h)
  rw [ConvexSubgroup.mem_comapUnitsWithZero, unitsWithZeroEquiv_mk0_restrict v h0 ha]
  refine characteristicSubgroup_le_characteristicSubgroupOfIdeal v I hfg
    (valueGroup_mk_mem_characteristicSubgroup_of_one_le_value h0 ?_)
  have hr : v.restrict 1 ≤ v.restrict a := by simpa using h1
  simpa using v.restrict_le_iff.mp hr

/-- The value monoid of the restricted valuation: `cΓ_v(I)`, transported onto the units of the
value monoid, with a zero adjoined. -/
-- Named rather than written inline because downstream statements need it as a
-- `LinearOrderedCommGroupWithZero`. `Valuation` asks only for the monoid class, so an inline
-- `WithZero …` elaborates with `WithZero`'s monoid instance, and then `CofinalValue`, which
-- needs the group class, cannot even be *stated* about the result -- a mismatch no `letI`
-- inside a later proof can repair.
abbrev RestrictedValues (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) : Type _ :=
  WithZero (ConvexSubgroup.comapUnitsWithZero (characteristicSubgroupOfIdeal v I hfg)).toSubgroup

/-- `RestrictedValues` is a linearly ordered commutative group with zero. -/
-- Registered explicitly so downstream statements find this instance rather than `WithZero`'s
-- monoid instance: without it the abbreviation unfolds and the monoid instance wins.
noncomputable instance instLinearOrderedCommGroupWithZeroRestrictedValues (v : Valuation A Γ₀)
    (I : Ideal A) (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    LinearOrderedCommGroupWithZero (RestrictedValues v I hfg) :=
  inferInstance

/-- **Wedhorn §7.1.2: the restriction `v ↦ v|cΓ_v(I)`.** Values whose unit lies in `cΓ_v(I)` are
kept; every other value is sent to `0`. -/
noncomputable def restrictToIdeal (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    Valuation A (RestrictedValues v I hfg) :=
  (v.restrict).restrictToConvex _ (mk0_restrict_mem_comapUnitsWithZero v I hfg)

/-! ### The restriction, characterised through `cΓ_v(I)`

`restrictToIdeal` keeps or discards a value according to membership in the *transported*
`cΓ_v(I)`, which is not the form a consumer holds: the introduction rules for `cΓ_v(I)` speak
about the value group. The bridge below converts between the two, and the lemmas after it are
stated so that no consumer has to unfold the definition or mention the transport. -/

/-- **The bridge.** A value's unit lies in the transported `cΓ_v(I)` exactly when the value,
read in the value group, lies in `cΓ_v(I)` itself. -/
theorem mk0_restrict_mem_comapUnitsWithZero_iff (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0) :
    Units.mk0 (v.restrict a) (fun h => h0 (v.restrict_eq_zero_iff.mp h)) ∈
        ConvexSubgroup.comapUnitsWithZero (characteristicSubgroupOfIdeal v I hfg) ↔
      valueGroup.mk (.ofClass v) 1 a (by simp) h0 ∈ characteristicSubgroupOfIdeal v I hfg := by
  rw [ConvexSubgroup.mem_comapUnitsWithZero, unitsWithZeroEquiv_mk0_restrict v h0 _]

/-- On a value kept by the restriction, the restriction is that value. -/
theorem restrictToIdeal_apply_of_mem (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A} (ha : v.restrict a ≠ 0)
    (hm : Units.mk0 (v.restrict a) ha ∈
      ConvexSubgroup.comapUnitsWithZero (characteristicSubgroupOfIdeal v I hfg)) :
    v.restrictToIdeal I hfg a =
      ((⟨Units.mk0 (v.restrict a) ha, hm⟩ :
        (ConvexSubgroup.comapUnitsWithZero
          (characteristicSubgroupOfIdeal v I hfg)).toSubgroup) : RestrictedValues v I hfg) :=
  _root_.Valuation.restrictToConvex_apply_of_mem _ _ _ ha hm

/-- Off `cΓ_v(I)`, the restriction vanishes. -/
@[simp]
theorem restrictToIdeal_apply_of_notMem (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A} (ha : v.restrict a ≠ 0)
    (hm : Units.mk0 (v.restrict a) ha ∉
      ConvexSubgroup.comapUnitsWithZero (characteristicSubgroupOfIdeal v I hfg)) :
    v.restrictToIdeal I hfg a = 0 :=
  _root_.Valuation.restrictToConvex_apply_of_notMem _ _ _ ha hm

/-- The restriction vanishes wherever `v` does. -/
@[simp]
theorem restrictToIdeal_apply_of_eq_zero (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a = 0) : v.restrictToIdeal I hfg a = 0 :=
  _root_.Valuation.restrictToConvex_apply_of_eq_zero _ _ _ (v.restrict_eq_zero_iff.mpr h0)

/-- **Where the restriction vanishes at a nonzero value**, stated through `cΓ_v(I)` itself.
`restrictToIdeal_eq_zero_iff` is the total form. -/
theorem restrictToIdeal_eq_zero_iff_of_ne (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0) :
    v.restrictToIdeal I hfg a = 0 ↔
      valueGroup.mk (.ofClass v) 1 a (by simp) h0 ∉ characteristicSubgroupOfIdeal v I hfg :=
  (_root_.Valuation.restrictToConvex_eq_zero_iff_of_ne _ _ _
      (fun h => h0 (v.restrict_eq_zero_iff.mp h))).trans
    (not_congr (mk0_restrict_mem_comapUnitsWithZero_iff v I hfg h0))

/-- **Where the restriction vanishes, totally**: at the zeros of `v`, and where `v` is nonzero
but its value escapes `cΓ_v(I)`. `restrictToIdeal_eq_zero_iff_of_ne` is the nonzero branch, in
the form consumers holding a nonvanishing hypothesis want. -/
@[simp]
theorem restrictToIdeal_eq_zero_iff (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (a : A) :
    v.restrictToIdeal I hfg a = 0 ↔ (MonoidWithZeroHom.ofClass v) a = 0 ∨
      ∃ h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0,
        valueGroup.mk (.ofClass v) 1 a (by simp) h0 ∉ characteristicSubgroupOfIdeal v I hfg := by
  by_cases h0 : (MonoidWithZeroHom.ofClass v) a = 0
  · simp [restrictToIdeal_apply_of_eq_zero v I hfg h0, h0]
  · rw [restrictToIdeal_eq_zero_iff_of_ne v I hfg h0]
    constructor
    · exact fun h => Or.inr ⟨h0, h⟩
    · rintro (hz | ⟨_, h'⟩)
      · exact absurd hz h0
      · exact h'

/-- A value at least `1` stays at least `1`: `cΓ_v(I)` keeps every attained value `≥ 1`. -/
theorem one_le_restrictToIdeal (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A} (h1 : 1 ≤ v.restrict a) :
    1 ≤ v.restrictToIdeal I hfg a :=
  _root_.Valuation.one_le_restrictToConvex _ _ _ h1

end TauCeti.Valuation
