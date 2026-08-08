/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Cofinal values and microbial valuations

Two conditions on the values of a valuation `v : Valuation A Γ₀` that control continuity
in the adic theory, following Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §4.3 and §7.1:

* a value `v a` is *cofinal* if its powers fall below every positive `γ : Γ₀` — the
  condition on ideals of definition in Wedhorn Lemma 7.1;
* `v` is *microbial* if every positive `γ : Γ₀` is bounded between `(v a)⁻¹` and `v a`
  for some `a` with `1 ≤ v a` — the elementwise reading of "the characteristic subgroup
  `cΓ_v` of Wedhorn 4.13 is the whole value group".

These are the two disjuncts of the membership criterion for `Spv (A, I)` in Wedhorn
Lemma 7.4, formalised here at the level of `Γ₀`-valued valuations with no topology on `A`.

## Main definitions

* `TauCeti.Valuation.CofinalValue v a` : Powers of `v a` fall below every positive value.
* `TauCeti.Valuation.characteristicSet v` : The set-with-zero underlying the
  characteristic subgroup `cΓ_v` of Wedhorn 4.13.
* `TauCeti.Valuation.IsMicrobial v` : Every positive value lies in the characteristic set.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, 4.13, Lemma 7.1, Lemma 7.4
-/

public section

namespace TauCeti.Valuation

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-! ### Cofinal values -/

/-- A value `v a` is **cofinal** if for every positive `γ : Γ₀` some power `(v a) ^ n`
lies strictly below `γ` (Wedhorn Lemma 7.1: the condition satisfied by the elements of an
ideal of definition). -/
def CofinalValue (v : Valuation A Γ₀) (a : A) : Prop :=
  ∀ γ : Γ₀, 0 < γ → ∃ n : ℕ, v a ^ n < γ

/-- A cofinal value is at most `1`: otherwise its powers stay above `1`. -/
theorem CofinalValue.le_one {v : Valuation A Γ₀} {a : A} (h : CofinalValue v a) :
    v a ≤ 1 := by
  by_contra h_gt
  push Not at h_gt
  obtain ⟨n, hn⟩ := h 1 zero_lt_one
  exact absurd hn (not_lt_of_ge (one_le_pow_of_one_le' h_gt.le n))

/-- Cofinality is downward closed in the value: a smaller value is cofinal whenever a
larger one is (Wedhorn Lemma 7.1). -/
theorem CofinalValue.of_le {v : Valuation A Γ₀} {a b : A} (h : CofinalValue v a)
    (hba : v b ≤ v a) : CofinalValue v b := fun γ hγ ↦
  let ⟨n, hn⟩ := h γ hγ
  ⟨n, lt_of_le_of_lt (pow_le_pow_left' hba n) hn⟩

/-! ### The characteristic set and microbial valuations -/

/-- The set `Γ_{v,≥1} ∩ im v` of Wedhorn 4.13: the values `1 ≤ γ` attained by `v`. This
is the generating set of the characteristic subgroup `cΓ_v`. -/
def imageGeOne (v : Valuation A Γ₀) : Set Γ₀ :=
  {γ : Γ₀ | 1 ≤ γ ∧ ∃ a : A, v a = γ}

/-- The set-with-zero underlying the **characteristic subgroup** `cΓ_v` of Wedhorn 4.13:
`0` together with the positive `γ` bounded between `(v a)⁻¹` and `v a` for some `a` with
`1 ≤ v a` — the convex hull of the attained values `≥ 1` and their inverses. -/
def characteristicSet (v : Valuation A Γ₀) : Set Γ₀ :=
  {γ : Γ₀ | γ = 0 ∨ (0 < γ ∧ ∃ a : A, 1 ≤ v a ∧ (v a)⁻¹ ≤ γ ∧ γ ≤ v a)}

/-- If `v` is bounded by `1`, the generating set of the characteristic subgroup is
trivial. -/
theorem imageGeOne_subset_singleton_of_le_one (v : Valuation A Γ₀)
    (h : ∀ a : A, v a ≤ 1) : imageGeOne v ⊆ {1} := by
  rintro _ ⟨hγ_ge, a, rfl⟩
  exact Set.mem_singleton_iff.mpr (le_antisymm (h a) hγ_ge)

/-- A valuation is **microbial** if every positive value of `Γ₀` is bounded between
`(v a)⁻¹` and `v a` for some `a` with `1 ≤ v a` — the elementwise form of
"`cΓ_v` is the whole value group" (Wedhorn 4.13 and the discussion around Lemma 7.4). -/
def IsMicrobial (v : Valuation A Γ₀) : Prop :=
  ∀ γ : Γ₀, 0 < γ → ∃ a : A, 1 ≤ v a ∧ (v a)⁻¹ ≤ γ ∧ γ ≤ v a

/-- Microbiality is exactly the statement that the characteristic set is everything. -/
theorem isMicrobial_iff_characteristicSet_eq_univ {v : Valuation A Γ₀} :
    IsMicrobial v ↔ characteristicSet v = Set.univ := by
  constructor
  · intro h
    refine Set.eq_univ_iff_forall.mpr fun γ ↦ ?_
    rcases eq_or_ne γ 0 with rfl | hγ
    · exact Or.inl rfl
    · exact Or.inr ⟨zero_lt_iff.mpr hγ, h γ (zero_lt_iff.mpr hγ)⟩
  · intro h γ hγ
    rcases Set.eq_univ_iff_forall.mp h γ with h0 | ⟨-, ha⟩
    · exact absurd h0 hγ.ne'
    · exact ha

/-- For a microbial valuation, every positive `γ` is dominated by some nonzero value:
the existence statement used in the microbial case of Wedhorn Lemma 7.10. -/
theorem IsMicrobial.exists_inv_le {v : Valuation A Γ₀} (h : IsMicrobial v) {γ : Γ₀}
    (hγ : 0 < γ) : ∃ t : A, v t ≠ 0 ∧ (v t)⁻¹ ≤ γ := by
  obtain ⟨a, ha_ge_one, ha_inv_le, -⟩ := h γ hγ
  exact ⟨a, (zero_lt_one.trans_le ha_ge_one).ne', ha_inv_le⟩

end TauCeti.Valuation
