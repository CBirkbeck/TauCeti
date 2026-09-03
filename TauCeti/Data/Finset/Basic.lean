/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Subsets of a finite type: how many there are, and how to sum over them

* `TauCeti.card_nonempty_finset` counts the nonempty finsets of a finite type.
* `TauCeti.sum_subtype_card_eq_sum_update` reindexes a sum over the subsets of size one less than
  `card ι` as a sum over `ι`: those subsets are exactly the complements of singletons, and
  overwriting a constant function on such a complement is updating it at the missing point.
-/

public section

namespace TauCeti

/-- **The number of nonempty subsets of a finite type is `2ⁿ - 1`.** The `2ⁿ` subsets of an
`n`-element type are the nonempty ones together with the empty set, so the nonempty ones number
`2ⁿ - 1`. -/
theorem card_nonempty_finset {ι : Type*} [Finite ι] :
    Nat.card {S : Finset ι // S.Nonempty} = 2 ^ Nat.card ι - 1 := by
  classical
  let := Fintype.ofFinite ι
  have h : Fintype.card {S : Finset ι // S.Nonempty} = 2 ^ Fintype.card ι - 1 := by
    rw [Fintype.card_subtype]
    simp_rw [Finset.nonempty_iff_ne_empty]
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_finset]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h]

/-- **Summing over the subsets of size one less than `card ι` is summing over the points.** Such a
subset is the complement of a singleton, and `Finset.piecewise` against such a complement is
`Function.update` at the missing point, so a sum of `F` over those subsets is a sum over `ι`. -/
theorem sum_subtype_card_eq_sum_update {ι α M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] {m : ℕ} (hm : Fintype.card ι = m + 1) (F : (ι → α) → M) (x y : α) :
    (∑ s : {s : Finset ι // s.card = m}, F (s.1.piecewise (fun _ ↦ x) fun _ ↦ y)) =
      ∑ i : ι, F (Function.update (fun _ ↦ x) i y) := by
  refine (Fintype.sum_bijective (fun a : ι ↦ ⟨{a}ᶜ, by
    rw [Finset.card_compl, Finset.card_singleton, hm]
    omega⟩) ?_ _ _ fun i ↦ ?_).symm
  · refine ⟨fun _ _ ↦ (Finset.singleton_injective <| compl_injective <| Subtype.ext_iff.mp ·), ?_⟩
    intro ⟨s, hs⟩
    have h : sᶜ.card = 1 := by
      rw [Finset.card_compl, hs, hm]
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    exact ⟨a, Subtype.ext (compl_eq_comm.mp ha)⟩
  · rw [Subtype.coe_mk, Finset.compl_singleton, Finset.piecewise_erase_univ]

end TauCeti
