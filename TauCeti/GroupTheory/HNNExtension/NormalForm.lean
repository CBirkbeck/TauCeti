/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.HNNExtension
import Mathlib.Tactic.Group

/-!
# Conjugating base elements by reduced words in an HNN extension

Let `HNNExtension G A B φ` be the HNN extension of `G` along an isomorphism `φ : A ≃* B` of
subgroups, with stable letter `t`, so that `t * a * t⁻¹ = φ a` for `a ∈ A`. Every element of the
HNN extension is the product of a reduced word. For `u = ±1` write `toSubgroup A B u` for the
associated subgroup of `t ^ u`, which is `A` for `u = 1` and `B` for `u = -1`, and
`toSubgroupEquiv φ u : toSubgroup A B u ≃* toSubgroup A B (-u)` for `φ` or `φ⁻¹`. Then
`t ^ u * a * (t ^ u)⁻¹ = toSubgroupEquiv φ u a` for every `a ∈ toSubgroup A B u`.

Britton's lemma (Mathlib's `HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq`) gives a converse
for conjugates. Let `w` be the product of a reduced word `h * t ^ u * ⋯` and `c` an element of
`G`. If `w⁻¹ * c * w ∈ G`, then `h⁻¹ * c * h ∈ toSubgroup A B (-u)`. In particular
`t ^ u * g * (t ^ u)⁻¹` lies in `G` exactly when `g ∈ toSubgroup A B u`.

## Main results

* `HNNExtension.exists_reducedWord_prod_eq`: every element is the product of a reduced word.
* `HNNExtension.NormalWord.ReducedWord.exists_head_eq_and_prod_eq_mul_of`: multiplying the
  product of a nonempty reduced word on the right by an element of `G` gives the product of a
  reduced word with the same head.
* `TauCeti.HNNExtension.t_zpow_mul_of_mul_t_zpow_inv`:
  `t ^ u * a * (t ^ u)⁻¹ = toSubgroupEquiv φ u a`.
* `TauCeti.HNNExtension.head_inv_mul_mul_head_mem_toSubgroup_neg`: if `w = h * t ^ u * ⋯` is
  reduced and `w⁻¹ * c * w ∈ G`, then `h⁻¹ * c * h ∈ toSubgroup A B (-u)`.
* `TauCeti.HNNExtension.t_zpow_mul_of_mul_t_zpow_inv_mem_range_iff`:
  `t ^ u * g * (t ^ u)⁻¹ ∈ G ↔ g ∈ toSubgroup A B u`.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer (1977), Chapter IV, §2
  (Britton's lemma).
-/

public section

open Subgroup

namespace HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- Every element of an HNN extension is the product of a reduced word. -/
theorem exists_reducedWord_prod_eq (x : HNNExtension G A B φ) :
    ∃ w : NormalWord.ReducedWord G A B, w.prod φ = x := by
  obtain ⟨d⟩ := NormalWord.TransversalPair.nonempty G A B
  -- The normal form `x • empty` of `x` has product `x` (`NormalWord.prod_smul`).
  exact ⟨(x • (NormalWord.empty : NormalWord d)).toReducedWord, by simp⟩

namespace NormalWord.ReducedWord

/-- Multiplying the product of a reduced word with at least one letter on the right by an element
of the base group gives the product of a reduced word with the same head. -/
theorem exists_head_eq_and_prod_eq_mul_of (w : NormalWord.ReducedWord G A B) (hw : w.toList ≠ [])
    (c : G) :
    ∃ w' : NormalWord.ReducedWord G A B, w'.head = w.head ∧ w'.prod φ = w.prod φ * of c := by
  obtain ⟨L, p, hL⟩ := (List.eq_nil_or_concat w.toList).resolve_left hw
  have hchain := w.chain
  rw [hL, List.concat_eq_append, List.isChain_append] at hchain
  refine ⟨⟨w.head, L ++ [(p.1, p.2 * c)], List.isChain_append.2
    ⟨hchain.1, List.isChain_singleton _, fun a ha b hb => ?_⟩⟩, rfl, ?_⟩
  · obtain rfl : b = (p.1, p.2 * c) := by simpa using hb.symm
    exact hchain.2.2 a ha p (by simp)
  · simp [NormalWord.ReducedWord.prod, hL, mul_assoc]

end NormalWord.ReducedWord

end HNNExtension

open HNNExtension

namespace TauCeti.HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- For `a` in the associated subgroup of `t ^ u`, `t ^ u * a * (t ^ u)⁻¹` is the image
`toSubgroupEquiv φ u a` of `a` in the associated subgroup of `t ^ (-u)`. -/
@[simp]
theorem t_zpow_mul_of_mul_t_zpow_inv (u : ℤˣ) (a : toSubgroup A B u) :
    (t : HNNExtension G A B φ) ^ (u : ℤ) * of (a : G) * (t ^ (u : ℤ))⁻¹ =
      of (toSubgroupEquiv φ u a : G) := by
  -- `toSubgroup A B 1` is `A` and `toSubgroup A B (-1)` is `B` by definition (`toSubgroup_one`,
  -- `toSubgroup_neg_one`), so `a` is an argument of `φ` or of `φ.symm`.
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [toSubgroupEquiv_one, Units.val_one, zpow_one]
    exact (equiv_eq_conj (φ := φ) a).symm
  · simp only [toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one, zpow_neg, zpow_one, inv_inv]
    exact (equiv_symm_eq_conj (φ := φ) a).symm

/-- **Britton's lemma for conjugates.** If `w = h * t ^ u * ⋯` is the product of a reduced word
and `w⁻¹ * c * w` lies in the base group for some `c` in the base group, then
`h⁻¹ * c * h` lies in the associated subgroup of `t ^ (-u)`. -/
theorem head_inv_mul_mul_head_mem_toSubgroup_neg {w : NormalWord.ReducedWord G A B} {u : ℤˣ}
    {g : G} {L : List (ℤˣ × G)} (hw : w.toList = (u, g) :: L) {c : G}
    (hc : (w.prod φ)⁻¹ * of c * w.prod φ ∈ (of : G →* HNNExtension G A B φ).range) :
    w.head⁻¹ * c * w.head ∈ toSubgroup A B (-u) := by
  obtain ⟨c', hc'⟩ := hc
  obtain ⟨w', hw'h, hw'⟩ := w.exists_head_eq_and_prod_eq_mul_of (φ := φ) (by simp [hw]) c'
  have h := (ReducedWord.map_fst_eq_and_of_prod_eq φ (w₁ := { w with head := c * w.head })
    (w₂ := w') ?_).2 u (by simp [hw])
  · simpa [hw'h, mul_assoc] using inv_mem h
  · rw [hw', hc']
    simp only [NormalWord.ReducedWord.prod, map_mul]
    group

/-- For `g` in the base group, `t ^ u * g * (t ^ u)⁻¹` lies in the base group exactly when `g` lies
in the associated subgroup of `t ^ u`. -/
theorem t_zpow_mul_of_mul_t_zpow_inv_mem_range_iff {u : ℤˣ} {g : G} :
    (t : HNNExtension G A B φ) ^ (u : ℤ) * of g * (t ^ (u : ℤ))⁻¹ ∈
      (of : G →* HNNExtension G A B φ).range ↔ g ∈ toSubgroup A B u := by
  refine ⟨fun h => ?_, fun hg => ⟨_, (t_zpow_mul_of_mul_t_zpow_inv u ⟨g, hg⟩).symm⟩⟩
  -- `(t ^ u)⁻¹` is the product of the reduced word with head `1` and the single letter
  -- `t ^ (-u)`.
  simpa using head_inv_mul_mul_head_mem_toSubgroup_neg (c := g)
    (w := ⟨1, [(-u, 1)], List.isChain_singleton _⟩) rfl
    (by simpa [NormalWord.ReducedWord.prod] using h)

end TauCeti.HNNExtension
