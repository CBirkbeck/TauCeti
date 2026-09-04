/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Algebra.Order.Group.ConvexSubgroup
public import TauCeti.RingTheory.Valuation.CharacteristicGroup

/-!
# Coarsening a valuation by a convex subgroup

Collapsing a convex subgroup `H` of the value units of `Γ₀` coarsens any `Γ₀`-valued
valuation: values are pushed along `Γ₀ ≃ WithZero Γ₀ˣ → WithZero (Γ₀ˣ ⧸ H)`, which is
monotone precisely because `H` is convex. The support is unchanged, bounds by `1` survive,
and a value that is at most `1` whose unit avoids `H` lands strictly below `1` — the three
facts the height-one generization of Wedhorn's Lemma 7.45 consumes.

## Main definitions

* `TauCeti.coarsenMapOfValueGroup` : the monoid-with-zero map
  `Γ₀ → WithZero (Γ₀ˣ ⧸ H.toSubgroup)`.
* `Valuation.coarsenByUnits` : the coarsened valuation.

## Main results

* `Valuation.coarsenByUnits_supp` : coarsening preserves the support.
* `Valuation.coarsenByUnits_lt_one_of_notMem` : the collapse detects non-membership — a value
  at most `1` whose unit avoids `H` drops strictly below `1`. (Bounds by `1` come from
  `coarsenMapOfValueGroup_monotone` directly; no specialization is exported for them.)
* `TauCeti.coarsenMapOfValueGroup_mul_inv_lt` : shrinking by a unit whose class exceeds `1`
  strictly decreases the coarsened value — how a strict inequality is recovered from a map that
  is only monotone.
* `Valuation.cofinalValue_coarsenByUnits_restrict` : coarsening by a proper convex subgroup
  preserves cofinality of a value. This needs no topology on `A`.

## Provenance

The coarsening construction itself is adapted from AINTLIB (see References),
`projects/AdicSpaces/Adic spaces/ValuationCoarsening.lean`: `TauCeti.coarsenMapOfValueGroup`,
`Valuation.coarsenByUnits` and the collapse statements about them are that file's, with its local
`WithZero.mapMonoidWithZeroHom` block replaced by Mathlib's `WithZero.map'` and the composite
shaped as in Mathlib's own `LinearOrderedCommGroupWithZero` locally-finite instance.

`Valuation.cofinalValue_coarsenByUnits_restrict` is not from that development. It is the
topology-free cofinality ingredient of Wedhorn's Remark 7.11(2), not the remark itself: the
continuity statement the remark makes is
`TauCeti.Huber.IsContinuous.coarsenByUnits_restrict` in
`TauCeti.RingTheory.Huber.Continuous.Coarsen`, which consumes this one. The order-level step it
rests on is `TauCeti.coarsenMapOfValueGroup_mul_inv_lt`, together with
`TauCeti.ConvexSubgroup.exists_one_lt_quotientMk`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), around Lemma 7.45.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/ValuationCoarsening.lean`.
-/

namespace TauCeti

public section

open TauCeti.ConvexSubgroup

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

open Classical in
/-- The coarsening map `Γ₀ → WithZero (Γ₀ˣ ⧸ H.toSubgroup)`: identify `Γ₀` with
`WithZero Γ₀ˣ` and collapse `H`. -/
noncomputable def coarsenMapOfValueGroup (H : ConvexSubgroup Γ₀ˣ) :
    Γ₀ →*₀ WithZero (Γ₀ˣ ⧸ H.toSubgroup) :=
  (WithZero.map' (QuotientGroup.mk' H.toSubgroup)).comp
    (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom

open Classical in
/-- The coarsening map is monotone; convexity of `H` is what orders the quotient. -/
theorem coarsenMapOfValueGroup_monotone (H : ConvexSubgroup Γ₀ˣ) :
    Monotone (coarsenMapOfValueGroup H) :=
  (WithZero.map'_mono H.quotientMk_monotone).comp
    (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toOrderIso.monotone

open Classical in
/-- The coarsening map sends the value of a unit to its class. -/
@[simp]
theorem coarsenMapOfValueGroup_apply_coe (H : ConvexSubgroup Γ₀ˣ) (g : Γ₀ˣ) :
    coarsenMapOfValueGroup H (g : Γ₀) = (QuotientGroup.mk' H.toSubgroup g :) := by
  have h : ((OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom (g : Γ₀))
      = (g : WithZero Γ₀ˣ) := WithZero.withZeroUnitsEquiv_symm_apply_coe g
  rw [coarsenMapOfValueGroup, MonoidWithZeroHom.comp_apply, h, WithZero.map'_coe]

open Classical in
/-- **Shrinking by a unit whose class exceeds `1` strictly decreases the coarsened value.** The
coarsening map is monotone but not strictly so; this is the step that recovers a strict
inequality from it. The unit whose class exceeds `1` is supplied by properness of the convex
subgroup, which the caller establishes. -/
theorem coarsenMapOfValueGroup_mul_inv_lt (H : ConvexSubgroup Γ₀ˣ) {d : Γ₀ˣ}
    (hd : 1 < QuotientGroup.mk' H.toSubgroup d) {g : Γ₀} (hg : g ≠ 0) :
    coarsenMapOfValueGroup H (g * (d : Γ₀)⁻¹) < coarsenMapOfValueGroup H g := by
  rw [map_mul, map_inv₀, coarsenMapOfValueGroup_apply_coe]
  refine mul_lt_of_lt_one_right (zero_lt_iff.mpr (by simpa using hg)) ?_
  exact_mod_cast inv_lt_one'.mpr hd

end

end TauCeti

namespace Valuation

public section

open TauCeti

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Coarsening a valuation by a convex subgroup of the units of its value monoid. -/
noncomputable def coarsenByUnits (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    Valuation R (WithZero (Γ₀ˣ ⧸ H.toSubgroup)) :=
  v.map (coarsenMapOfValueGroup H) (coarsenMapOfValueGroup_monotone H)

/-- Coarsening applies the coarsening map to each value. -/
@[simp]
theorem coarsenByUnits_apply (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) (r : R) :
    v.coarsenByUnits H r = coarsenMapOfValueGroup H (v r) :=
  Valuation.map_apply _ _ _ _

/-- A value at most `1` whose unit avoids `H` lands strictly below `1` after coarsening. -/
theorem coarsenByUnits_lt_one_of_notMem (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    {a : R} (ha_ne : v a ≠ 0) (ha_le : v a ≤ 1)
    (hm : Units.mk0 (v a) ha_ne ∉ H) : v.coarsenByUnits H a < 1 := by
  have hle : Units.mk0 (v a) ha_ne ≤ 1 := by
    rw [← Units.val_le_val, Units.val_mk0, Units.val_one]
    exact ha_le
  rw [coarsenByUnits_apply, ← Units.val_mk0 ha_ne, coarsenMapOfValueGroup_apply_coe]
  exact_mod_cast H.quotientMk_lt_one_of_notMem hle hm

section Supp

-- `Valuation.supp` is defined only over a commutative ring, so this one statement asks for
-- more than the rest of the file; the construction above needs no commutativity.
variable {S : Type*} [CommRing S] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Coarsening preserves the support. -/
@[simp]
theorem coarsenByUnits_supp (v : Valuation S Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    (v.coarsenByUnits H).supp = v.supp := by
  -- the coarsening map is a `→*₀` out of a `GroupWithZero`, so Mathlib's `map_eq_zero` already
  -- says it kills no nonzero value; nothing about the construction has to be reopened
  ext r
  simp only [mem_supp_iff, coarsenByUnits_apply, map_eq_zero]

end Supp

open MonoidWithZeroHom in
/-- **Coarsening by a proper convex subgroup preserves cofinality of a value.** This is the half of
Wedhorn Remark 7.11(2) that properness is needed for: the coarsening map is monotone but not
strictly so, and properness is exactly what supplies the room to recover a strict inequality. -/
theorem cofinalValue_coarsenByUnits_restrict {A : Type*} [Ring A] {v : Valuation A Γ₀}
    {H : ConvexSubgroup (ValueGroup₀ (.ofClass v))ˣ} (hH : H ≠ ⊤) {a : A}
    (hcof : CofinalValue v a) : CofinalValue (v.restrict.coarsenByUnits H) a := by
  -- Every positive element of the coarsened value group is a ratio of attained values; shrinking
  -- that ratio by `d⁻¹` turns the monotone image of a cofinal power into a strict bound.
  obtain ⟨d, hx⟩ := H.exists_one_lt_quotientMk hH
  rw [cofinalValue_iff]
  intro γ hγ
  obtain ⟨r, q, hr, hq, hrq⟩ :=
    (v.restrict.coarsenByUnits H).exists_div_eq_of_unit (Units.mk0 γ hγ.ne')
  simp only [Units.val_mk0] at hrq
  have hrv : v.restrict r ≠ 0 := fun h ↦ by simp [h] at hr
  have hqv : v.restrict q ≠ 0 := fun h ↦ by simp [h] at hq
  obtain ⟨n, hn⟩ := cofinalValue_iff.mp hcof
    (v.restrict r / v.restrict q * (d : ValueGroup₀ (.ofClass v))⁻¹)
    (by simp [zero_lt_iff, hrv, hqv, Units.ne_zero d])
  refine ⟨n, ?_⟩
  -- Both sides are coarsenings of values of `v`, so the comparison happens in `Γ₀`'s coarsened
  -- value monoid: monotonicity carries the cofinal power across, and the `d⁻¹` factor is what
  -- turns the resulting `≤` into `<`.
  have hγ' : ValueGroup₀.embedding γ =
      coarsenMapOfValueGroup H (v.restrict r / v.restrict q) := by
    rw [← hrq, map_div₀, Valuation.embedding_restrict, coarsenByUnits_apply,
      Valuation.embedding_restrict, coarsenByUnits_apply, ← map_div₀]
  rw [← map_pow, Valuation.restrict_lt_iff_lt_embedding, hγ']
  calc (v.restrict.coarsenByUnits H) (a ^ n)
      = coarsenMapOfValueGroup H (v.restrict a ^ n) := by rw [coarsenByUnits_apply, map_pow]
    _ ≤ coarsenMapOfValueGroup H (v.restrict r / v.restrict q * (d : ValueGroup₀ (.ofClass v))⁻¹) :=
        coarsenMapOfValueGroup_monotone H hn.le
    _ < coarsenMapOfValueGroup H (v.restrict r / v.restrict q) :=
        coarsenMapOfValueGroup_mul_inv_lt H hx (div_ne_zero hrv hqv)

end

end Valuation
