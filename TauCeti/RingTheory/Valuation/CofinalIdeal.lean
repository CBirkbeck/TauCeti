/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Algebra.Order.Group.Cofinal
public import TauCeti.RingTheory.Valuation.CharacteristicGroup
public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# The ideal of cofinal values

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Lemma 7.1.** For a valuation `v` on a
commutative ring and a convex subgroup `H` of its value group strictly containing the
characteristic subgroup `cΓ_v`, the elements whose value is cofinal for `H` form a radical
ideal. The cofinality predicate itself and its closure properties need only a ring;
commutativity enters exactly where the ideal is formed. This is the object Wedhorn's §7.1
uses to reduce the construction of `cΓ_v(I)`
(Definition 7.3) to a finite generating set, and it is used twice in the proof of Lemma 7.2:
once to pass from generators to the whole ideal, and once to replace `I` by its radical.

Cofinality here is stated for a value that may vanish, since `0` is cofinal for every
subgroup — that is why the vanishing case is a case split in the proofs below rather than
something derivable from cofinality.

## Main definitions

* `TauCeti.Valuation.CofinalValueFor v H a` : The powers of `v a` fall below every member
  of the convex subgroup `H` of the value group.
* `TauCeti.Valuation.cofinalIdeal v hH` : Those elements, as an ideal.

## Main results

* `TauCeti.Valuation.cofinalValueFor_iff_isCofinalElement` : For a non-vanishing value, the
  valuation-side predicate agrees with the group-side `IsCofinalElement` on the value group.
  This is what lets Wedhorn Proposition 1.20 apply.
* `TauCeti.Valuation.cofinalValueFor_pow_iff` : The ideal is radical.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Lemma 7.1
-/

public section

namespace TauCeti.Valuation

open MonoidWithZeroHom

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- `v a` is **cofinal for the convex subgroup `H`** of the value group: its powers fall
below every member of `H` (Wedhorn Definition 1.16, at a value that may vanish). -/
def CofinalValueFor (v : Valuation A Γ₀)
    (H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))) (a : A) : Prop :=
  ∀ h ∈ H, ∃ n : ℕ, v.restrict a ^ n < (h : ValueGroup₀ (.ofClass v))

/-- The defining property of cofinality relative to a convex subgroup. -/
@[simp]
theorem cofinalValueFor_def {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {a : A} :
    CofinalValueFor v H a ↔
      ∀ h ∈ H, ∃ n : ℕ, v.restrict a ^ n < (h : ValueGroup₀ (.ofClass v)) :=
  Iff.rfl

/-- Cofinality for `H` is downward closed in the value. -/
theorem CofinalValueFor.of_le {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {a b : A}
    (h : CofinalValueFor v H a) (hba : v b ≤ v a) : CofinalValueFor v H b := fun γ hγ ↦
  let ⟨n, hn⟩ := h γ hγ
  ⟨n, lt_of_le_of_lt (pow_le_pow_left' (v.restrict_le_iff.mpr hba) n) hn⟩

/-- A vanishing value is cofinal for every convex subgroup (Wedhorn's remark after
Definition 1.16: the adjoined base `0` is cofinal for every subgroup). -/
theorem cofinalValueFor_of_eq_zero {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {a : A} (ha : v a = 0) :
    CofinalValueFor v H a := by
  intro h _
  refine ⟨1, ?_⟩
  rw [pow_one, v.restrict_eq_zero_iff.mpr ha]
  exact zero_lt_iff.mpr WithZero.coe_ne_zero

/-- Zero has cofinal value. -/
theorem cofinalValueFor_zero (v : Valuation A Γ₀)
    (H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))) : CofinalValueFor v H 0 :=
  cofinalValueFor_of_eq_zero (map_zero v)

/-- A sum of cofinal-value elements has cofinal value: `v (a + b) ≤ max (v a) (v b)`. -/
theorem CofinalValueFor.add {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {a b : A}
    (ha : CofinalValueFor v H a) (hb : CofinalValueFor v H b) :
    CofinalValueFor v H (a + b) := by
  rcases le_total (v a) (v b) with hab | hab
  · exact hb.of_le ((map_add_le_max v a b).trans (max_le hab le_rfl))
  · exact ha.of_le ((map_add_le_max v a b).trans (max_le le_rfl hab))

/-- Multiplying by an element of value at most `1` preserves cofinality. -/
theorem CofinalValueFor.mul_of_le_one {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {a b : A}
    (ha : CofinalValueFor v H a) (hb : v b ≤ 1) : CofinalValueFor v H (b * a) :=
  ha.of_le (by
    rw [map_mul]
    exact mul_le_of_le_one_left' hb)

/-- For a nonzero value, cofinality for `H` is cofinality of the corresponding element of
the value group: the bridge between the valuation-side and group-side predicates. -/
theorem cofinalValueFor_iff_isCofinalElement {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {a : A}
    (h : (MonoidWithZeroHom.ofClass v) a ≠ 0) :
    CofinalValueFor v H a ↔
      TauCeti.IsCofinalElement H.toSubgroup (valueGroup.mk (.ofClass v) 1 a (by simp) h) := by
  rw [cofinalValueFor_def, TauCeti.isCofinalElement_def]
  refine forall_congr' fun g ↦ forall_congr' fun _ ↦ exists_congr fun n ↦ ?_
  rw [v.restrict_eq_mk h, ← WithZero.coe_pow, WithZero.coe_lt_coe]

/-- **Wedhorn Lemma 7.1, the multiplicative step.** If `cΓ_v` is strictly smaller than `H`
and `v a` is cofinal for `H`, then so is `v (b * a)` for every `b` — the case `1 < v b`
going through the characteristic subgroup and Wedhorn Remark 1.20. -/
theorem CofinalValueFor.mul {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) {a : A} (ha : CofinalValueFor v H a) (b : A) :
    CofinalValueFor v H (b * a) := by
  rcases le_or_gt (v b) 1 with hb | hb
  · exact ha.mul_of_le_one hb
  · -- `v b > 1` is an attained value `≥ 1`, hence lies in `cΓ_v ⊊ H`.
    have hb0 : (MonoidWithZeroHom.ofClass v) b ≠ 0 := by
      simpa using (zero_lt_one.trans hb).ne'
    rcases eq_or_ne (v a) 0 with ha0' | ha0'
    · exact cofinalValueFor_of_eq_zero (by rw [map_mul, ha0', mul_zero])
    have ha0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := by simpa using ha0'
    have hab0 : (MonoidWithZeroHom.ofClass v) (b * a) ≠ 0 := by
      simpa [map_mul] using mul_ne_zero hb0 ha0
    have hmem : valueGroup.mk (.ofClass v) 1 b (by simp) hb0 ∈ characteristicSubgroup v := by
      refine valueGroup_mk_mem_characteristicSubgroup hb0 ?_
      rw [← WithZero.coe_le_coe, ← v.restrict_eq_mk hb0]
      have : v.restrict 1 ≤ v.restrict b := v.restrict_le_iff.mpr (by simpa using hb.le)
      simpa using this
    rw [cofinalValueFor_iff_isCofinalElement hab0]
    have := ((cofinalValueFor_iff_isCofinalElement ha0).mp ha).mul_of_lt_of_mem hH hmem
    have hcoe : ((valueGroup.mk (.ofClass v) 1 (b * a) (by simp) hab0 :
        valueGroup (.ofClass v)) : ValueGroup₀ (.ofClass v))
        = ((valueGroup.mk (.ofClass v) 1 b (by simp) hb0 *
            valueGroup.mk (.ofClass v) 1 a (by simp) ha0 :
            valueGroup (.ofClass v)) : ValueGroup₀ (.ofClass v)) := by
      rw [← v.restrict_eq_mk hab0, WithZero.coe_mul, ← v.restrict_eq_mk hb0,
        ← v.restrict_eq_mk ha0, ← map_mul]
    rw [WithZero.coe_inj.mp hcoe]
    exact this

/-- A cofinal value lies strictly below `1`. -/
theorem CofinalValueFor.lt_one {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {a : A}
    (h : CofinalValueFor v H a) : v.restrict a < 1 := by
  obtain ⟨n, hn⟩ := h 1 (one_mem H)
  simp only [WithZero.coe_one] at hn
  by_contra hge
  push Not at hge
  exact absurd hn (not_lt.mpr (one_le_pow_of_one_le' hge n))

/-- A power has cofinal value exactly when the element does (for a positive exponent):
the ingredient of `rad c = c` in Wedhorn Lemma 7.1. -/
theorem cofinalValueFor_pow_iff {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {a : A} {m : ℕ} (hm : 0 < m) :
    CofinalValueFor v H (a ^ m) ↔ CofinalValueFor v H a := by
  constructor
  · intro h g hg
    obtain ⟨n, hn⟩ := h g hg
    refine ⟨m * n, ?_⟩
    rwa [map_pow, ← pow_mul] at hn
  · intro h g hg
    obtain ⟨n, hn⟩ := h g hg
    refine ⟨n, lt_of_le_of_lt ?_ hn⟩
    rw [map_pow, ← pow_mul]
    exact pow_le_pow_right_of_le_one' h.lt_one.le (Nat.le_mul_of_pos_left n hm)

/-! ### The ideal of cofinal values -/

section Ideal

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Wedhorn Lemma 7.1.** For a convex subgroup `H` of the value group strictly containing
the characteristic subgroup, the elements whose value is cofinal for `H` form an ideal. -/
def cofinalIdeal (v : Valuation A Γ₀)
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) : Ideal A where
  carrier := {a | CofinalValueFor v H a}
  zero_mem' := cofinalValueFor_zero v H
  add_mem' ha hb := CofinalValueFor.add ha hb
  smul_mem' b _ ha := CofinalValueFor.mul hH ha b

@[simp]
theorem mem_cofinalIdeal {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    {hH : characteristicSubgroup v < H} {a : A} :
    a ∈ cofinalIdeal v hH ↔ CofinalValueFor v H a :=
  Iff.rfl

end Ideal

end TauCeti.Valuation
