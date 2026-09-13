/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Cosets of the image of a subgroup in a quotient group

For a normal subgroup `N` of `G` and an **arbitrary** subgroup `H`, the cosets of the image
`H·N/N` in `G ⧸ N` are the cosets of `H ⊔ N` in `G`. This is Noether's third isomorphism
theorem with the normality of the upper subgroup dropped: `H` is unconstrained, so neither
`(G ⧸ N) ⧸ H·N/N` nor `G ⧸ (H ⊔ N)` need carry a group structure, and what remains is a
bijection of coset spaces. Mathlib's `QuotientGroup.quotientQuotientEquivQuotient` is the
group isomorphism this generalises, stated for `N ≤ M` with `M` normal.

The bijection is what a family or a sum indexed by cosets needs — an index equality only says
the two index *types* have the same cardinality, not which coset of one corresponds to which
coset of the other. The index equality follows from it.

## Main results

* `Subgroup.mk_mem_map_mk'_iff`: the class of `g` modulo `N` lies in the image of `H` exactly
  when `g` lies in `H ⊔ N`.
* `QuotientGroup.quotientQuotientEquivQuotientSup`: the bijection
  `(G ⧸ N) ⧸ H.map (mk' N) ≃ G ⧸ (H ⊔ N)`, sending the class of `g` to the class of `g`.
* `Subgroup.index_map_mk'_eq_index_sup`: the index of the image of `H` in `G ⧸ N` is the
  index of `H ⊔ N` in `G` — the cardinality shadow of that bijection.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- **Membership in the image of a subgroup under a quotient map.** The class of `g` modulo `N`
lies in the image of `H` exactly when `g` lies in `H ⊔ N`: a witness `h ∈ H` with `⟦h⟧ = ⟦g⟧`
is the same data as a factorisation `g = h * n` with `n ∈ N`. -/
@[to_additive /-- **Membership in the image of a subgroup under a quotient map.** The class of `g`
modulo `N` lies in the image of `H` exactly when `g` lies in `H ⊔ N`. -/]
theorem _root_.Subgroup.mk_mem_map_mk'_iff {H N : Subgroup G} [N.Normal] {g : G} :
    (g : G ⧸ N) ∈ H.map (QuotientGroup.mk' N) ↔ g ∈ H ⊔ N := by
  simp only [Subgroup.mem_map, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_sup_of_normal_right]
  exact ⟨fun ⟨h, hh, hg⟩ ↦ ⟨h, hh, h⁻¹ * g, hg, mul_inv_cancel_left h g⟩,
    fun ⟨h, hh, n, hn, hg⟩ ↦ ⟨h, hh, by rw [← hg]; simpa using hn⟩⟩

/-- **The third isomorphism theorem for coset spaces.** For a normal `N` and an *arbitrary*
subgroup `H`, the cosets of the image of `H` in `G ⧸ N` are the cosets of `H ⊔ N` in `G`, both
directions sending the class of `g` to the class of `g`.

Mathlib's `QuotientGroup.quotientQuotientEquivQuotient` is the group isomorphism this
generalises: it asks for `N ≤ M` with `M` normal, so that both sides are groups and the map is a
homomorphism. Here neither side need be a group — `H` is unconstrained — and what survives is the
bijection of coset spaces, which is what a coset-indexed sum or family needs.
`Subgroup.index_map_mk'_eq_index_sup` is its cardinality shadow, and is now read off it. -/
@[to_additive /-- **The third isomorphism theorem for coset spaces**, additive version: for a
normal `N` and an arbitrary subgroup `H`, the cosets of the image of `H` in `G ⧸ N` are the
cosets of `H ⊔ N` in `G`. -/]
def _root_.QuotientGroup.quotientQuotientEquivQuotientSup (H N : Subgroup G) [N.Normal] :
    (G ⧸ N) ⧸ H.map (QuotientGroup.mk' N) ≃ G ⧸ (H ⊔ N) where
  toFun := Quotient.lift (Subgroup.quotientMapOfLE (le_sup_right : N ≤ H ⊔ N)) <| by
    refine Quotient.ind fun x ↦ Quotient.ind fun y hxy ↦ ?_
    have h := QuotientGroup.leftRel_apply.mp hxy
    simp only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h
    exact QuotientGroup.eq.mpr (Subgroup.mk_mem_map_mk'_iff.mp h)
  invFun := Quotient.lift (fun g : G ↦ ((g : G ⧸ N) : (G ⧸ N) ⧸ H.map (QuotientGroup.mk' N)))
    fun x y hxy ↦ QuotientGroup.eq.mpr <| by
      simpa only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] using
        Subgroup.mk_mem_map_mk'_iff.mpr (QuotientGroup.leftRel_apply.mp hxy)
  left_inv := Quotient.ind fun x ↦ QuotientGroup.induction_on x fun _ ↦ rfl
  right_inv := fun q ↦ QuotientGroup.induction_on q fun _ ↦ rfl

@[to_additive (attr := simp), simp]
theorem _root_.QuotientGroup.quotientQuotientEquivQuotientSup_mk_mk (H N : Subgroup G) [N.Normal]
    (g : G) :
    QuotientGroup.quotientQuotientEquivQuotientSup H N
        ((g : G ⧸ N) : (G ⧸ N) ⧸ H.map (QuotientGroup.mk' N)) = (g : G ⧸ (H ⊔ N)) := (rfl)

/-- The index of the image of a subgroup in a quotient is the index of its join with the
quotienting subgroup: the two coset spaces are in bijection, by
`QuotientGroup.quotientQuotientEquivQuotientSup`. -/
@[to_additive (attr := simp), simp]
theorem _root_.Subgroup.index_map_mk'_eq_index_sup (H N : Subgroup G) [N.Normal] :
    (H.map (QuotientGroup.mk' N)).index = (H ⊔ N).index :=
  Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotientSup H N)

end TauCeti
