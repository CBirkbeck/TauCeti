/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas
public import TauCeti.GroupTheory.SpecificGroups.Cyclic.OrderCount

/-!
# Elements with a prescribed divisibility condition on their order

In the cyclic auxiliary group used by the Chebotarev crossing, the useful tags are the elements
whose order is divisible by the order of the chosen Frobenius element. This file gives that finite
carrier together with its membership and divisibility API.

## Main definitions

* `TauCeti.NumberField.Chebotarev.taggedElements`: elements whose order is divisible by a given
  natural number.

## Main results

* `TauCeti.NumberField.Chebotarev.mem_taggedElements_iff`: the defining membership condition.
* `TauCeti.NumberField.Chebotarev.taggedElements_subset_of_dvd`: divisibility makes the tag carrier
  shrink.
* `TauCeti.NumberField.Chebotarev.card_taggedElements_eq_sum_totient`: the exact cyclic count,
  expressed as a sum of Euler totients over the allowed orders;
* `TauCeti.NumberField.Chebotarev.le_card_taggedElements_cyclic`: a uniform lower bound for that
  count, over `ℝ`.

## References

The crossing construction follows R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
-/

public section

open scoped BigOperators

namespace TauCeti.NumberField.Chebotarev

open Finset Nat

/-- The elements of a finite group whose order is divisible by `f`.

The carrier is deliberately a `Finset`, so the tags can be indexed by their order. -/
noncomputable def taggedElements {H : Type*} [Group H] [Fintype H] (f : ℕ) : Finset H :=
  Finset.univ.filter fun τ ↦ f ∣ orderOf τ

/-- Membership in `taggedElements`, unfolded to the order divisibility condition. -/
@[simp]
theorem mem_taggedElements_iff {H : Type*} [Group H] [Fintype H] {f : ℕ} {τ : H} :
    τ ∈ taggedElements f ↔ f ∣ orderOf τ := by
  simp [taggedElements]

/-- A stronger divisibility requirement gives a smaller tagged carrier. -/
theorem taggedElements_subset_of_dvd {H : Type*} [Group H] [Fintype H] {f g : ℕ} (hfg : f ∣ g) :
    taggedElements (H := H) g ⊆ taggedElements (H := H) f := by
  unfold taggedElements
  exact Finset.monotone_filter_right Finset.univ fun _ _ h => hfg.trans h

/-- Every element is tagged for the vacuous order condition `f = 1`. -/
@[simp]
theorem taggedElements_one {H : Type*} [Group H] [Fintype H] :
    taggedElements (H := H) 1 = Finset.univ := by
  ext τ
  simp [taggedElements]

/-- In a finite cyclic group, count the tagged elements by their exact orders. -/
theorem card_taggedElements_eq_sum_totient {H : Type*} [Group H] [Fintype H] [IsCyclic H]
    (f : ℕ) :
    (taggedElements (H := H) f).card =
      ∑ d ∈ (Fintype.card H).divisors.filter (f ∣ ·), Nat.totient d := by
  unfold taggedElements
  exact IsCyclic.card_filter_dvd_orderOf_eq_sum_totient f

/-- **The tagged elements of a cyclic group are a fixed proportion of it.**  When `f ^ r` divides
the order of `H`, at least `(1 - 2 ^ (-r)) ^ #f.primeFactors` of the elements of `H` have order
divisible by `f`.

This restates `IsCyclic.le_card_filter_dvd_orderOf` for the `taggedElements` carrier and over
`ℝ`, which is where the density statements consuming it live.  No positivity hypothesis on `f` is
needed: `f ^ r` divides `Nat.card H`, which is nonzero, so `f` is nonzero already. -/
theorem le_card_taggedElements_cyclic {H : Type*} [Group H] [Fintype H] [IsCyclic H] (f r : ℕ)
    (hrpos : 0 < r) (hf : f ^ r ∣ Nat.card H) :
    (1 - (2 : ℝ) ^ (-(r : ℤ))) ^ f.primeFactors.card * (Nat.card H : ℝ) ≤
      ((taggedElements (H := H) f).card : ℝ) := by
  rw [Nat.card_eq_fintype_card] at hf ⊢
  have hset : taggedElements f = ({τ : H | f ∣ orderOf τ} : Finset H) := Finset.ext fun τ ↦ by simp
  have hR := (Rat.cast_le (K := ℝ)).mpr (IsCyclic.le_card_filter_dvd_orderOf hrpos hf)
  push_cast at hR
  rwa [hset, ← inv_zpow', zpow_natCast]

end TauCeti.NumberField.Chebotarev
