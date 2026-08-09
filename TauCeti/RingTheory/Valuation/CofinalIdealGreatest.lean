/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Valuation.CofinalIdeal

/-!
# The greatest convex subgroup for which an ideal is cofinal

Scaffolding for **Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Lemma 7.2**: when `v(I)` misses
the characteristic subgroup, there is a *greatest* convex subgroup `H` for which every `v a`,
`a ∈ I`, is cofinal. That existence statement is what makes Definition 7.3 well posed.

This file collects the predicates the statement needs and the parts that hold in general;
the existence proof itself reduces to a finite generating set and is completed separately.

## Main definitions

* `TauCeti.Valuation.IdealCofinalFor v H I` : every element of `I` has value cofinal for `H`.
* `TauCeti.Valuation.IdealMeetsCharacteristic v I` : `v(I)` meets `cΓ_v`, the branch condition
  of Wedhorn Definition 7.3.
* `TauCeti.Valuation.IsGreatestIdealCofinal v I H` : `H` is greatest with that property.
* `TauCeti.Valuation.valueSet v I` : the nonzero values of `v` on `I`, the set Wedhorn takes
  the maximum over.

## Main results

* `TauCeti.Valuation.idealCofinalFor_iff_forall_isCofinalElement` : the ideal condition is
  cofinality of every nonzero value, as an element of the value group.
* `TauCeti.Valuation.isGreatestIdealCofinal_closure_singleton` : the core step of Lemma 7.2 —
  a greatest value below `1` generates the greatest convex subgroup for which `I` is cofinal.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Lemma 7.2, Definition 7.3
-/

public section

namespace TauCeti.Valuation

open MonoidWithZeroHom

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The predicate cut out by Wedhorn Lemma 7.2: every element of `I` has value cofinal
for `H`. -/
def IdealCofinalFor (v : Valuation A Γ₀)
    (H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))) (I : Ideal A) : Prop :=
  ∀ a ∈ I, CofinalValueFor v H a

@[simp]
theorem idealCofinalFor_def {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {I : Ideal A} :
    IdealCofinalFor v H I ↔ ∀ a ∈ I, CofinalValueFor v H a :=
  Iff.rfl

/-- The trivial ideal is cofinal for every convex subgroup. -/
theorem idealCofinalFor_bot (v : Valuation A Γ₀)
    (H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))) : IdealCofinalFor v H ⊥ := by
  intro a ha
  exact cofinalValueFor_of_eq_zero (by simpa using congrArg v (Ideal.mem_bot.mp ha))

/-- The condition is antitone in the ideal. -/
theorem IdealCofinalFor.mono {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {I J : Ideal A}
    (h : IdealCofinalFor v H J) (hIJ : I ≤ J) : IdealCofinalFor v H I :=
  fun a ha ↦ h a (hIJ ha)

/-- Below the strict-containment threshold, the ideal condition says exactly that `I` is
contained in the cofinality ideal of Lemma 7.1. -/
theorem idealCofinalFor_iff_le_cofinalIdeal {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) {I : Ideal A} :
    IdealCofinalFor v H I ↔ I ≤ cofinalIdeal v hH :=
  ⟨fun h _ hx ↦ mem_cofinalIdeal.mpr (h _ hx), fun h _ hx ↦ mem_cofinalIdeal.mp (h hx)⟩

/-- The values of `I` meet the characteristic subgroup: the first branch of Wedhorn
Definition 7.3. -/
def IdealMeetsCharacteristic (v : Valuation A Γ₀) (I : Ideal A) : Prop :=
  ∃ (a : A) (_ : a ∈ I) (h : (MonoidWithZeroHom.ofClass v) a ≠ 0),
    valueGroup.mk (.ofClass v) 1 a (by simp) h ∈ characteristicSubgroup v

@[simp]
theorem idealMeetsCharacteristic_def {v : Valuation A Γ₀} {I : Ideal A} :
    IdealMeetsCharacteristic v I ↔
      ∃ (a : A) (_ : a ∈ I) (h : (MonoidWithZeroHom.ofClass v) a ≠ 0),
        valueGroup.mk (.ofClass v) 1 a (by simp) h ∈ characteristicSubgroup v :=
  Iff.rfl

/-- An attained value `≥ 1` always meets the characteristic subgroup — so under Wedhorn's
disjointness hypothesis every element of `I` has value strictly below `1`, the observation
recorded after Lemma 7.2. -/
theorem lt_one_of_not_idealMeetsCharacteristic {v : Valuation A Γ₀} {I : Ideal A}
    (hdisj : ¬ IdealMeetsCharacteristic v I) {a : A} (haI : a ∈ I) : v a < 1 := by
  by_contra hge
  push Not at hge
  have ha0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := by
    simpa using (zero_lt_one.trans_le hge).ne'
  refine hdisj ⟨a, haI, ha0, mem_characteristicSubgroup_of_restrict ?_ (v.restrict_eq_mk ha0)⟩
  rw [← WithZero.coe_le_coe, ← v.restrict_eq_mk ha0]
  have : v.restrict 1 ≤ v.restrict a := v.restrict_le_iff.mpr (by simpa using hge)
  simpa using this

/-- Cofinality for a larger convex subgroup implies cofinality for a smaller one: the
monotonicity that makes the family in Wedhorn Lemma 7.2 downward closed. -/
theorem CofinalValueFor.mono {v : Valuation A Γ₀}
    {H K : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {a : A}
    (h : CofinalValueFor v K a) (hHK : H ≤ K) : CofinalValueFor v H a :=
  cofinalValueFor_def.mpr fun g hg ↦ cofinalValueFor_def.mp h g (hHK hg)

/-- The ideal condition inherits that monotonicity. -/
theorem IdealCofinalFor.mono_subgroup {v : Valuation A Γ₀}
    {H K : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {I : Ideal A}
    (h : IdealCofinalFor v K I) (hHK : H ≤ K) : IdealCofinalFor v H I :=
  fun a ha ↦ (h a ha).mono hHK

/-- Wedhorn Lemma 7.2's greatest element, when it exists, is characterized by being an
upper bound within the family — the statement the case split of Definition 7.3 consumes. -/
def IsGreatestIdealCofinal (v : Valuation A Γ₀) (I : Ideal A)
    (H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))) : Prop :=
  IdealCofinalFor v H I ∧ ∀ K, IdealCofinalFor v K I → K ≤ H

theorem IsGreatestIdealCofinal.unique {v : Valuation A Γ₀} {I : Ideal A}
    {H K : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : IsGreatestIdealCofinal v I H) (hK : IsGreatestIdealCofinal v I K) : H = K :=
  le_antisymm (hK.2 H hH.1) (hH.2 K hK.1)

/-- For the zero ideal the greatest element is the whole value group (Wedhorn's first
reduction: "if `v(I) = {0}` we may choose `H = Γ_v`"). -/
theorem isGreatestIdealCofinal_bot (v : Valuation A Γ₀) :
    IsGreatestIdealCofinal v ⊥ ⊤ :=
  ⟨idealCofinalFor_bot v ⊤, fun _ _ ↦ le_top⟩

/-! ### Reduction to the value set -/

/-- The nonzero values attained by `v` on an ideal, as a subset of the value group. This is
the set Wedhorn takes the maximum over in the proof of Lemma 7.2. -/
def valueSet (v : Valuation A Γ₀) (I : Ideal A) : Set (valueGroup (.ofClass v)) :=
  {γ | ∃ a ∈ I, v.restrict a = (γ : ValueGroup₀ (.ofClass v))}

@[simp]
theorem mem_valueSet {v : Valuation A Γ₀} {I : Ideal A} {γ : valueGroup (.ofClass v)} :
    γ ∈ valueSet v I ↔ ∃ a ∈ I, v.restrict a = (γ : ValueGroup₀ (.ofClass v)) :=
  Iff.rfl

/-- **The bridge from the ideal to the group.** An ideal is cofinal for `H` exactly when every
one of its nonzero values is a cofinal *element* of the value group. The vanishing values need
no condition, since `0` is cofinal for every subgroup — which is why they are excluded from
`valueSet` rather than constrained. -/
theorem idealCofinalFor_iff_forall_isCofinalElement {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {I : Ideal A} :
    IdealCofinalFor v H I ↔
      ∀ γ ∈ valueSet v I, TauCeti.IsCofinalElement H.toSubgroup γ := by
  constructor
  · rintro hI γ ⟨a, haI, ha⟩
    have h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := by
      intro hz
      exact absurd (ha ▸ v.restrict_eq_zero_iff.mpr hz) WithZero.coe_ne_zero
    have := (cofinalValueFor_iff_isCofinalElement h0).mp (hI a haI)
    have hmk : valueGroup.mk (.ofClass v) 1 a (by simp) h0 = γ := by
      have := (v.restrict_eq_mk h0).symm.trans ha
      exact_mod_cast this
    exact hmk ▸ this
  · intro hS a haI
    by_cases h0 : (MonoidWithZeroHom.ofClass v) a = 0
    · exact cofinalValueFor_of_eq_zero h0
    · refine (cofinalValueFor_iff_isCofinalElement h0).mpr (hS _ ⟨a, haI, ?_⟩)
      exact v.restrict_eq_mk h0

/-! ### The core step of Wedhorn Lemma 7.2 -/

/-- **Wedhorn Lemma 7.2, core step.** If the nonzero values of `I` have a greatest element `h`,
necessarily below `1`, then the convex subgroup it generates is the *greatest* one for which
`I` is cofinal.

The inversion is the point: below `1` a smaller value generates a larger convex subgroup, so
the largest value gives the smallest subgroup — and that is the one every value is cofinal for.
This is why Wedhorn's proof takes `max { v t : t ∈ T }` over a finite generating set. -/
theorem isGreatestIdealCofinal_closure_singleton {v : Valuation A Γ₀} {I : Ideal A}
    {h : valueGroup (.ofClass v)} (hh : IsGreatest (valueSet v I) h) (hlt : h < 1) :
    IsGreatestIdealCofinal v I (TauCeti.ConvexSubgroup.closure {h}) := by
  obtain ⟨hmem, hub⟩ := TauCeti.isGreatest_convexSubgroup_isCofinalElement hh hlt
  refine ⟨idealCofinalFor_iff_forall_isCofinalElement.mpr hmem, fun K hK ↦ ?_⟩
  exact hub (idealCofinalFor_iff_forall_isCofinalElement.mp hK)

end TauCeti.Valuation
