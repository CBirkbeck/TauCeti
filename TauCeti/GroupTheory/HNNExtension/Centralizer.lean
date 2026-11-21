/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.HNNExtension.NormalForm
public import TauCeti.GroupTheory.TrivialIntersection

/-!
# Centralizers of base elements in an HNN extension

Let `HNNExtension B A A' φ` be the HNN extension of a group `B` along an isomorphism
`φ : A ≃* A'` of subgroups, with stable letter `t`, so that `t * a * t⁻¹ = φ a` for `a ∈ A`.
Suppose that `A` and `A'` are malnormal in `B` and that no nontrivial element of `A'` is conjugate
in `B` into `A`. Then a nontrivial element `x` of `B` commutes, in the HNN extension, only with
elements of `B`: its centralizer is the image of its centralizer in `B`
(`TauCeti.HNNExtension.centralizer_of_eq_map`).

In the Bass–Serre tree, `x` fixes the vertex of `B`, and by the two conditions it fixes at most
one edge there: two fixed edges at a vertex would conjugate a nontrivial element of `A'` into `A`,
or a nontrivial element of `A` or of `A'` back into the same subgroup by an element outside it. At
the other end of a fixed edge `x` acts as a nontrivial element of `A` or of `A'`, which for the
same reason fixes no further edge. So the fixed subtree of `x` is either the vertex of `B` or a
single edge at it. An element commuting with `x` preserves this subtree, and since the HNN
extension acts on its tree without inversions, it fixes the vertex of `B`.

Both conditions are needed. For `A = A' = B` and `φ` the identity, both malnormal, the stable
letter commutes with every element of `B`. For `A = ⟨a⟩` and `A' = ⟨b a b⁻¹⟩` in the free group
`B = F(a, b)`, with `φ` the conjugation by `b`, the element `b⁻¹ * t` commutes with `a`. For
`B = ⟨a, r | [a, r] = 1⟩ ∗ ⟨e⟩`, `A = ⟨a⟩` (not malnormal), `A' = ⟨e⟩` and `φ a = e`, the element
`t * r * t⁻¹` commutes with `e`.

## Main results

* `TauCeti.HNNExtension.isTISubgroup_toSubgroup`: if `A` and `A'` are malnormal, so are the
  associated subgroups of `t` and `t⁻¹`.
* `TauCeti.HNNExtension.eq_one_of_mul_mul_inv_mem_toSubgroup_neg`: if no nontrivial element of
  `A'` is conjugate into `A`, no nontrivial element of the associated subgroup of `t ^ u` is
  conjugate into that of `t ^ (-u)`.
* `TauCeti.HNNExtension.prod_inv_mul_mul_prod_notMem_range`: if the associated subgroup of `t ^ u`
  is malnormal and no nontrivial element of `A'` is conjugate into `A`, then `w⁻¹ * x * w ∉ B` for
  every nontrivial `x` in that subgroup and every reduced word `w` with at least one stable letter
  such that `t ^ u * w` is reduced.
* `TauCeti.HNNExtension.centralizer_of_eq_map`: the centralizer of a nontrivial base element, when
  the associated subgroups are malnormal and no nontrivial element of one is conjugate into the
  other.

## Implementation notes

The proof uses Britton's lemma in the form of
`TauCeti.HNNExtension.head_inv_mul_mul_head_mem_toSubgroup_neg` (from Mathlib's
`HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq`): if `w = h * t ^ u * ⋯` is the product of a
reduced word and `w⁻¹ * c * w ∈ B` for some `c ∈ B`, then `h⁻¹ * c * h` lies in the associated
subgroup of `t ^ (-u)`. Write an element commuting with `x` as the product `w` of a reduced word,
so that `w⁻¹ * x * w = x`. If the word has no stable letters, `w` lies in `B`. Otherwise
`w = h * t ^ u * z` with `z` the product of the rest of the word. Then `h⁻¹ * x * h` lies in the
associated subgroup of `t ^ (-u)`, and `x₁ = t ^ (-u) * (h⁻¹ * x * h) * t ^ u` is a nontrivial
element of the associated subgroup of `t ^ u` (`TauCeti.HNNExtension.t_zpow_mul_of_mul_t_zpow_inv`)
with `z⁻¹ * x₁ * z = x`. If `z = b` is a single letter of `B`, then `x` is conjugate in `B` both to
`h⁻¹ * x * h` and to `x₁`, which contradicts the hypothesis on conjugates. Otherwise
`z = b * t ^ u' * ⋯` with `t ^ u * z` reduced, and
`TauCeti.HNNExtension.prod_inv_mul_mul_prod_notMem_range` shows that `z⁻¹ * x₁ * z` is not in `B`.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer (1977), Chapter IV, §2
  (Britton's lemma).
* J.-P. Serre, *Trees*, Springer (1980), Chapter I, §1.4 (HNN extensions) and §4 (their trees).
-/

public section

open Subgroup HNNExtension NormalWord

namespace TauCeti.HNNExtension

variable {B : Type*} [Group B] {A A' : Subgroup B} {φ : A ≃* A'}

/-- If `A` and `A'` are malnormal, so is the associated subgroup of every `t ^ u`. -/
theorem isTISubgroup_toSubgroup (hA : IsTISubgroup A) (hA' : IsTISubgroup A') (u : ℤˣ) :
    IsTISubgroup (toSubgroup A A' u) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using hA
  · simpa using hA'

/-- If no nontrivial element of `A'` is conjugate into `A`, no nontrivial element of the associated
subgroup of `t ^ u` is conjugate into that of `t ^ (-u)`. -/
theorem eq_one_of_mul_mul_inv_mem_toSubgroup_neg
    (hAA' : ∀ g : B, ∀ a ∈ A', g * a * g⁻¹ ∈ A → a = 1) {u : ℤˣ} {a g : B}
    (ha : a ∈ toSubgroup A A' u) (hga : g * a * g⁻¹ ∈ toSubgroup A A' (-u)) : a = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact conj_eq_one_iff.1 (hAA' g⁻¹ _ (by simpa using hga) (by simpa [mul_assoc] using ha))
  · exact hAA' g a (by simpa using ha) (by simpa using hga)

/-- Let `x` be a nontrivial element of the associated subgroup of `t ^ u`, and `w` the product of
a reduced word `h * t ^ u' * ⋯` such that `t ^ u * w` is still reduced. If the associated subgroup
of `t ^ u` is malnormal and no nontrivial element of `A'` is conjugate into `A`, then
`w⁻¹ * x * w` is not in the base group. -/
theorem prod_inv_mul_mul_prod_notMem_range (hAA' : ∀ g : B, ∀ a ∈ A', g * a * g⁻¹ ∈ A → a = 1)
    {u : ℤˣ} (hTI : IsTISubgroup (toSubgroup A A' u)) {x : B} (hx : x ∈ toSubgroup A A' u)
    (hx1 : x ≠ 1) {w : ReducedWord B A A'} {u' : ℤˣ} {g : B} {L : List (ℤˣ × B)}
    (hw : w.toList = (u', g) :: L) (hred : w.head ∈ toSubgroup A A' u → u = u') :
    (w.prod φ)⁻¹ * of x * w.prod φ ∉ (of : B →* HNNExtension B A A' φ).range := by
  -- `h⁻¹ * x * h` lies in the associated subgroup of `t ^ (-u')`. This contradicts the hypothesis
  -- on conjugates if `u' = u`, and malnormality if `u' = -u`, since then `h` is outside the
  -- associated subgroup of `t ^ u`.
  intro hmem
  have hx₂ := head_inv_mul_mul_head_mem_toSubgroup_neg hw hmem
  by_cases hu : u' = u
  · subst hu
    exact hx1 (eq_one_of_mul_mul_inv_mem_toSubgroup_neg hAA' (g := w.head⁻¹) hx
      (by simpa using hx₂))
  · refine hx1 (hTI.eq_one (g := w.head⁻¹) (by simpa using fun hb => hu (hred hb).symm) hx ?_)
    rw [Int.units_ne_iff_eq_neg.1 hu, neg_neg] at hx₂
    simpa using hx₂

/-- If `A` and `A'` are malnormal and no nontrivial element of `A'` is conjugate into `A`, a
reduced word whose product commutes with a nontrivial element `x` of the base group has no
letters. -/
private theorem toList_eq_nil_of_prod_inv_mul_mul_prod_eq (hA : IsTISubgroup A)
    (hA' : IsTISubgroup A') (hAA' : ∀ g : B, ∀ a ∈ A', g * a * g⁻¹ ∈ A → a = 1) {x : B}
    (hx : x ≠ 1) {w : ReducedWord B A A'} (hw : (w.prod φ)⁻¹ * of x * w.prod φ = of x) :
    w.toList = [] := by
  rcases hL : w.toList with _ | ⟨⟨u, b⟩, L⟩
  · rfl
  exfalso
  -- With `w = h * t ^ u * z`, `h⁻¹ * x * h` lies in the associated subgroup of `t ^ (-u)`, and
  -- `x₁ = t ^ (-u) * (h⁻¹ * x * h) * t ^ u` in that of `t ^ u`, with `z⁻¹ * x₁ * z = x`.
  have hx₀ := head_inv_mul_mul_head_mem_toSubgroup_neg hL ⟨x, hw.symm⟩
  set x₁ : B := (toSubgroupEquiv φ (-u) ⟨_, hx₀⟩ : B)
  have hx₁ : x₁ ∈ toSubgroup A A' u := by simpa using (toSubgroupEquiv φ (-u) ⟨_, hx₀⟩).property
  have hchain := w.chain
  rw [hL, List.isChain_cons] at hchain
  let z : ReducedWord B A A' := ⟨b, L, hchain.2⟩
  have hz : (z.prod φ)⁻¹ * of x₁ * z.prod φ = of x := by
    have hwz : w.prod φ = of w.head * t ^ (u : ℤ) * z.prod φ := by
      simp [ReducedWord.prod, z, hL, mul_assoc]
    rw [hwz] at hw
    rw [← hw, ← t_zpow_mul_of_mul_t_zpow_inv]
    simp only [map_mul, map_inv, Units.val_neg]
    group
  have hx₁1 : x₁ ≠ 1 := fun h1 =>
    hx (by simpa [h1, map_eq_one_iff _ (of_injective (φ := φ))] using hz.symm)
  rcases hL' : L with _ | ⟨⟨u', b'⟩, L'⟩
  · -- `x` is conjugate in `B` both to `h⁻¹ * x * h` and to `x₁`, which is impossible.
    have hzb : z.prod φ = of b := by simp [ReducedWord.prod, z, hL']
    rw [hzb, ← map_inv, ← map_mul, ← map_mul] at hz
    refine hx₁1 (eq_one_of_mul_mul_inv_mem_toSubgroup_neg hAA' (g := w.head⁻¹ * b⁻¹) hx₁ ?_)
    rw [← of_injective φ hz] at hx₀
    simpa [mul_assoc] using hx₀
  · exact prod_inv_mul_mul_prod_notMem_range hAA' (isTISubgroup_toSubgroup hA hA' u) hx₁ hx₁1
      (w := z) hL' (fun hb => hchain.1 (u', b') (by simp [hL']) hb) ⟨x, hz.symm⟩

variable (φ) in
/-- **Centralizers in an HNN extension with malnormal, non-conjugate associated subgroups.** If
`A` and `A'` are malnormal and no nontrivial element of `A'` is conjugate into `A`, the
centralizer in `HNNExtension B A A' φ` of a nontrivial element `x` of `B` is the image of its
centralizer in `B`. -/
theorem centralizer_of_eq_map (hA : IsTISubgroup A) (hA' : IsTISubgroup A')
    (hAA' : ∀ g : B, ∀ a ∈ A', g * a * g⁻¹ ∈ A → a = 1) {x : B} (hx : x ≠ 1) :
    centralizer {(of x : HNNExtension B A A' φ)} = (centralizer {x}).map of := by
  refine le_antisymm (fun y hy => ?_) ?_
  · -- Write `y` as a reduced word; it has no letters, so it is an element of `B`.
    obtain ⟨w, rfl⟩ := exists_reducedWord_prod_eq y
    have hw : w.prod φ = of w.head := by
      simp [ReducedWord.prod, toList_eq_nil_of_prod_inv_mul_mul_prod_eq hA hA' hAA' hx (w := w)
        (mem_centralizer_singleton_iff.1 hy).inv_mul_cancel]
    refine ⟨w.head, mem_centralizer_singleton_iff.2 (of_injective φ ?_), hw.symm⟩
    simpa [hw] using (mem_centralizer_singleton_iff.1 hy).eq
  · simpa using map_centralizer_le_centralizer_image {x} (of : B →* HNNExtension B A A' φ)

/-! ### Examples -/

/-- With trivial associated subgroups the HNN extension is the free product `B ∗ ⟨t⟩`, and a
nontrivial element of `B` has the same centralizer there as in `B`. -/
example {x : B} (hx : x ≠ 1) :
    centralizer {(of x : HNNExtension B ⊥ ⊥ (.refl _))} = (centralizer {x}).map of :=
  centralizer_of_eq_map _ .bot .bot (fun _ _ ha _ => by simpa using ha) hx

/-- The hypothesis on conjugates cannot be dropped: for `A = A' = B` and the identity of `B`, both
malnormal, the stable letter commutes with every element of `B` but does not lie in `B`. -/
example (x : B) : ∃ y ∈ centralizer {(of x : HNNExtension B ⊤ ⊤ (.refl _))},
    y ∉ (of : B →* HNNExtension B ⊤ ⊤ (.refl _)).range := by
  refine ⟨t, mem_centralizer_singleton_iff.2 ?_, fun ⟨g, hg⟩ => ?_⟩
  · simpa [commute_iff_eq] using t_mul_of (φ := .refl (⊤ : Subgroup B)) ⟨x, mem_top x⟩
  · simpa using congrArg (lift (1 : B →* Multiplicative ℤ) (.ofAdd 1) fun _ => by simp) hg.symm

end TauCeti.HNNExtension
