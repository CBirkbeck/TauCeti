/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Convex subgroups of linearly ordered commutative groups

A subgroup of a linearly ordered commutative group is *convex* if it contains every element
lying between two of its members. Convex subgroups are the kernels of the order-compatible
quotients of the value group of a valuation: the quotient by a convex subgroup carries a
linear order making it an ordered group again, and any two convex subgroups are comparable.
This file develops the basic theory following Wedhorn, *Adic Spaces* (arXiv:1910.05934v1),
§1.4 and §7.1; the convex subgroup `cΓ_v(I)` of Wedhorn Definition 7.3 is built from
`minContain` in the valuation-spectrum development.

## Main definitions

* `TauCeti.ConvexSubgroup Γ` : The type of order-convex subgroups of `Γ`.
* `TauCeti.ConvexSubgroup.quotientLinearOrder` : The linear order on `Γ ⧸ H.toSubgroup`
  induced by a convex subgroup `H`, with `IsOrderedMonoid` compatibility.
* `TauCeti.ConvexSubgroup.minContain S` : The smallest convex subgroup containing a set.
* `TauCeti.ConvexSubgroup.maxAvoid hγ` : The largest convex subgroup avoiding `γ ≠ 1`.
* `TauCeti.ConvexSubgroup.comap` : The preimage of a convex subgroup under a monotone
  group homomorphism.

## Main results

* `TauCeti.ConvexSubgroup.le_total_of_convex` : Convex subgroups are totally ordered by
  inclusion.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §1.4, §7.1
-/

public section

namespace TauCeti

variable (Γ : Type*) [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

/-- A **convex subgroup** of a linearly ordered commutative group `Γ` is a subgroup
that is order-convex: if `a ≤ x ≤ b` and `a, b ∈ H`, then `x ∈ H`. -/
structure ConvexSubgroup extends Subgroup Γ where
  convex' : ∀ {a b x : Γ}, a ∈ carrier → b ∈ carrier → a ≤ x → x ≤ b → x ∈ carrier

namespace ConvexSubgroup

variable {Γ}

instance : SetLike (ConvexSubgroup Γ) Γ where
  coe H := H.carrier
  coe_injective := by
    intro ⟨H₁, _⟩ ⟨H₂, _⟩ h
    congr 1
    exact Subgroup.ext (Set.ext_iff.mp h)

instance : SubgroupClass (ConvexSubgroup Γ) Γ where
  mul_mem {H} := H.toSubgroup.mul_mem'
  one_mem {H} := H.toSubgroup.one_mem'
  inv_mem {H} := H.toSubgroup.inv_mem'

omit [IsOrderedMonoid Γ] in
@[ext]
theorem ext {H₁ H₂ : ConvexSubgroup Γ} (h : ∀ x, x ∈ H₁ ↔ x ∈ H₂) : H₁ = H₂ :=
  SetLike.ext h

omit [IsOrderedMonoid Γ] in
/-- Convexity: if `a, b ∈ H` and `a ≤ x ≤ b`, then `x ∈ H`. -/
theorem convex (H : ConvexSubgroup Γ) {a b x : Γ} (ha : a ∈ H) (hb : b ∈ H)
    (h₁ : a ≤ x) (h₂ : x ≤ b) : x ∈ H :=
  H.convex' ha hb h₁ h₂

omit [IsOrderedMonoid Γ] in
/-- A convex subgroup contains every element between `1` and one of its members. -/
theorem mem_of_one_le_le {H : ConvexSubgroup Γ} {x h : Γ}
    (hh : h ∈ H) (h1 : 1 ≤ x) (hx : x ≤ h) : x ∈ H :=
  H.convex (one_mem H) hh h1 hx

omit [IsOrderedMonoid Γ] in
/-- A convex subgroup contains every element between one of its members and `1`. -/
theorem mem_of_le_le_one {H : ConvexSubgroup Γ} {x h : Γ}
    (hh : h ∈ H) (hx : h ≤ x) (h1 : x ≤ 1) : x ∈ H :=
  H.convex hh (one_mem H) hx h1

/-- The trivial subgroup `{1}` is convex. -/
instance : Bot (ConvexSubgroup Γ) where
  bot :=
    { toSubgroup := ⊥
      convex' := by
        intro a b x ha hb h₁ h₂
        have ha' : a = 1 := Subgroup.mem_bot.mp ha
        have hb' : b = 1 := Subgroup.mem_bot.mp hb
        exact Subgroup.mem_bot.mpr (le_antisymm (h₂.trans hb'.le) (ha'.ge.trans h₁)) }

/-- The full group is a convex subgroup. -/
instance : Top (ConvexSubgroup Γ) where
  top :=
    { toSubgroup := ⊤
      convex' := fun _ _ _ _ ↦ trivial }

omit [IsOrderedMonoid Γ] in
@[simp]
theorem mem_bot {x : Γ} : x ∈ (⊥ : ConvexSubgroup Γ) ↔ x = 1 :=
  Subgroup.mem_bot

omit [IsOrderedMonoid Γ] in
@[simp]
theorem mem_top {x : Γ} : x ∈ (⊤ : ConvexSubgroup Γ) :=
  trivial

omit [IsOrderedMonoid Γ] in
theorem inv_mem_iff_mem {H : ConvexSubgroup Γ} {γ : Γ} : γ⁻¹ ∈ H ↔ γ ∈ H :=
  ⟨fun h ↦ inv_inv γ ▸ inv_mem h, inv_mem⟩

/-- Convex subgroups are ordered by inclusion. -/
instance : PartialOrder (ConvexSubgroup Γ) where
  le H₁ H₂ := ∀ x, x ∈ H₁ → x ∈ H₂
  le_refl _ _ hx := hx
  le_trans _ _ _ h₁₂ h₂₃ x hx := h₂₃ x (h₁₂ x hx)
  le_antisymm _ _ h₁₂ h₂₁ := ext fun _ ↦ ⟨h₁₂ _, h₂₁ _⟩

instance : OrderBot (ConvexSubgroup Γ) where
  bot_le H _ hx := mem_bot.mp hx ▸ one_mem H

instance : OrderTop (ConvexSubgroup Γ) where
  le_top _ _ _ := mem_top

/-! ### Elements outside a convex subgroup -/

omit [IsOrderedMonoid Γ] in
/-- An excluded element below `1` lies below every member. -/
theorem lt_of_not_mem_of_lt_one (H : ConvexSubgroup Γ) {γ : Γ} (hγ : γ ∉ H) (hγ1 : γ < 1)
    {h : Γ} (hh : h ∈ H) : γ < h := by
  by_contra hle
  push Not at hle
  exact hγ (H.convex' hh (one_mem H) hle hγ1.le)

omit [IsOrderedMonoid Γ] in
/-- An excluded element above `1` lies above every member. -/
theorem lt_of_not_mem_of_one_lt (H : ConvexSubgroup Γ) {γ : Γ} (hγ : γ ∉ H) (hγ1 : 1 < γ)
    {h : Γ} (hh : h ∈ H) : h < γ := by
  by_contra hle
  push Not at hle
  exact hγ (H.convex' (one_mem H) hh hγ1.le hle)

omit [IsOrderedMonoid Γ] in
/-- Elements above an excluded element above `1` are excluded, by convexity. -/
theorem not_mem_of_not_mem_of_one_lt_le (H : ConvexSubgroup Γ)
    {γ : Γ} (hγ : γ ∉ H) (hγ1 : 1 < γ) {x : Γ} (hγx : γ ≤ x) : x ∉ H :=
  fun hx ↦ hγ (H.convex (one_mem H) hx hγ1.le hγx)

omit [IsOrderedMonoid Γ] in
/-- Elements below an excluded element below `1` are excluded, by convexity. -/
theorem not_mem_of_not_mem_of_le_lt_one (H : ConvexSubgroup Γ)
    {γ : Γ} (hγ : γ ∉ H) (hγ1 : γ < 1) {x : Γ} (hxγ : x ≤ γ) : x ∉ H :=
  fun hx ↦ hγ (H.convex hx (one_mem H) hxγ hγ1.le)

/-! ### The quotient linear order -/

/-- The condition `c ≤ 1 ∨ c ∈ H` is invariant under multiplication by members of `H`. -/
private theorem le_one_or_mem_mul_iff (H : ConvexSubgroup Γ) (c k : Γ)
    (hk : k ∈ H.toSubgroup) :
    (c ≤ 1 ∨ c ∈ H.toSubgroup) ↔ (c * k ≤ 1 ∨ c * k ∈ H.toSubgroup) := by
  by_cases hc : (c : Γ) ∈ H
  · exact ⟨fun _ ↦ .inr (H.toSubgroup.mul_mem hc hk), fun _ ↦ .inr hc⟩
  · have hck : c * k ∉ H := by
      intro hmem
      have := H.toSubgroup.mul_mem hmem (H.toSubgroup.inv_mem hk)
      simp only [mul_inv_cancel_right] at this
      exact hc this
    simp only [show ¬(c ∈ H.toSubgroup) from hc, show ¬(c * k ∈ H.toSubgroup) from hck,
      or_false]
    constructor
    · intro h1
      exact le_of_lt (lt_inv_iff_mul_lt_one.mp (H.lt_of_not_mem_of_lt_one hc
        (lt_of_le_of_ne h1 fun h ↦ hc (h ▸ H.toSubgroup.one_mem)) (inv_mem hk)))
    · intro h1
      by_contra hc1
      push Not at hc1
      exact absurd h1 (not_le.mpr
        (inv_lt_iff_one_lt_mul.mp (H.lt_of_not_mem_of_one_lt hc hc1 (inv_mem hk))))

/-- The quotient by a convex subgroup is ordered by `[a] ≤ [b]` iff `b⁻¹ * a ≤ 1` or
`b⁻¹ * a ∈ H`. -/
instance quotientLE (H : ConvexSubgroup Γ) : LE (Γ ⧸ H.toSubgroup) where
  le x y := Quotient.liftOn₂' x y (fun a b ↦ b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H.toSubgroup)
    (fun a₁ b₁ a₂ b₂ ha hb ↦ by
      rw [QuotientGroup.leftRel_apply] at ha hb
      have hk : (b₁⁻¹ * b₂)⁻¹ * (a₁⁻¹ * a₂) ∈ H.toSubgroup :=
        H.toSubgroup.mul_mem (H.toSubgroup.inv_mem hb) ha
      have hb₂a₂ : b₂⁻¹ * a₂ = (b₁⁻¹ * a₁) * ((b₁⁻¹ * b₂)⁻¹ * (a₁⁻¹ * a₂)) := by
        simp only [mul_inv_rev, inv_inv, ← mul_assoc]
        simp [mul_comm, mul_left_comm, mul_assoc]
      rw [hb₂a₂]
      exact propext (le_one_or_mem_mul_iff H _ _ hk))

/-- The defining unfolding of `≤` on the quotient by a convex subgroup. -/
theorem quotient_le_iff (H : ConvexSubgroup Γ) (a b : Γ) :
    ((a : Γ ⧸ H.toSubgroup) ≤ (b : Γ ⧸ H.toSubgroup)) ↔
      (b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H.toSubgroup) :=
  Iff.rfl

private theorem quotient_le_total (H : ConvexSubgroup Γ) (a b : Γ) :
    (a : Γ ⧸ H.toSubgroup) ≤ b ∨ (b : Γ ⧸ H.toSubgroup) ≤ a := by
  rw [quotient_le_iff, quotient_le_iff]
  by_cases hm : b⁻¹ * a ∈ H.toSubgroup
  · exact .inl (.inr hm)
  · have hne : b⁻¹ * a ≠ 1 := fun h ↦ hm (h ▸ H.toSubgroup.one_mem)
    rcases lt_or_gt_of_ne hne with h | h
    · exact .inl (.inl h.le)
    · refine .inr (.inl (le_of_lt ?_))
      rw [show a⁻¹ * b = (b⁻¹ * a)⁻¹ by simp [mul_inv_rev, inv_inv]]
      exact inv_lt_one_of_one_lt h

private theorem quotient_le_trans (H : ConvexSubgroup Γ) {a b c : Γ}
    (hxy : (a : Γ ⧸ H.toSubgroup) ≤ b) (hyz : (b : Γ ⧸ H.toSubgroup) ≤ c) :
    (a : Γ ⧸ H.toSubgroup) ≤ c := by
  rw [quotient_le_iff] at hxy hyz ⊢
  have hca : c⁻¹ * a = (c⁻¹ * b) * (b⁻¹ * a) := by simp [mul_assoc, mul_inv_cancel_left]
  rw [hca]
  rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
  · exact .inl (mul_le_one' hyz hxy)
  · rw [mul_comm]
    exact (le_one_or_mem_mul_iff H _ _ hyz).mp (.inl hxy)
  · exact (le_one_or_mem_mul_iff H _ _ hxy).mp (.inl hyz)
  · exact .inr (H.toSubgroup.mul_mem hyz hxy)

private theorem quotient_le_antisymm (H : ConvexSubgroup Γ) {a b : Γ}
    (hxy : (a : Γ ⧸ H.toSubgroup) ≤ b) (hyx : (b : Γ ⧸ H.toSubgroup) ≤ a) :
    (a : Γ ⧸ H.toSubgroup) = b := by
  rw [quotient_le_iff] at hxy hyx
  apply QuotientGroup.eq.mpr
  rcases hxy with hxy | hxy
  · rcases hyx with hyx | hyx
    · have h1 : 1 ≤ b⁻¹ * a := by
        rw [show b⁻¹ * a = (a⁻¹ * b)⁻¹ by simp [mul_inv_rev, inv_inv]]
        exact one_le_inv_of_le_one hyx
      rw [show a⁻¹ * b = (b⁻¹ * a)⁻¹ by simp [mul_inv_rev, inv_inv],
        inv_eq_one.mpr (le_antisymm hxy h1)]
      exact H.toSubgroup.one_mem
    · exact hyx
  · rw [show a⁻¹ * b = (b⁻¹ * a)⁻¹ by simp [mul_inv_rev, inv_inv]]
    exact H.toSubgroup.inv_mem hxy

/-- The quotient of `Γ` by a convex subgroup `H` is linearly ordered:
`[a] ≤ [b]` iff `b⁻¹ * a ≤ 1` or `b⁻¹ * a ∈ H`. -/
noncomputable instance quotientLinearOrder (H : ConvexSubgroup Γ) :
    LinearOrder (Γ ⧸ H.toSubgroup) where
  le_refl x := by
    induction x using Quotient.inductionOn with
    | _ a => exact .inl (inv_mul_cancel a).le
  le_trans x y z hxy hyz := by
    induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
    induction z using Quotient.inductionOn with | _ c =>
    exact quotient_le_trans H hxy hyz
  le_antisymm x y hxy hyx := by
    induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
    exact quotient_le_antisymm H hxy hyx
  le_total x y := by
    induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
    exact quotient_le_total H a b
  toDecidableLE := Classical.decRel _
  toDecidableEq := Classical.decEq _
  toDecidableLT := Classical.decRel _

/-- The quotient linear order is compatible with the group operation. -/
instance quotientIsOrderedMonoid (H : ConvexSubgroup Γ) :
    IsOrderedMonoid (Γ ⧸ H.toSubgroup) where
  mul_le_mul_left a b hab c := by
    induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
    induction c using Quotient.inductionOn with | _ c =>
    rw [show ((a : Γ ⧸ H.toSubgroup) * c) = (a * c : Γ) from rfl,
      show ((b : Γ ⧸ H.toSubgroup) * c) = (b * c : Γ) from rfl, quotient_le_iff]
    rw [quotient_le_iff] at hab
    have h : (b * c)⁻¹ * (a * c) = b⁻¹ * a := by simp [mul_inv_rev, mul_comm, mul_assoc]
    rw [h]
    exact hab

/-! ### Total ordering of convex subgroups -/

/-- Any two convex subgroups of a linearly ordered commutative group are comparable. -/
theorem le_total_of_convex (H₁ H₂ : ConvexSubgroup Γ) : H₁ ≤ H₂ ∨ H₂ ≤ H₁ := by
  by_contra h
  push Not at h
  obtain ⟨hne₁, hne₂⟩ := h
  obtain ⟨a, haH₁, haH₂⟩ := Set.not_subset.mp (show ¬(H₁ : Set Γ) ⊆ H₂ from hne₁)
  have ha1 : a ≠ 1 := fun h ↦ haH₂ (h ▸ one_mem H₂)
  refine hne₂ fun b hb ↦ ?_
  have hainv : a⁻¹ ∉ H₂ := inv_mem_iff_mem.not.mpr haH₂
  rcases lt_or_gt_of_ne ha1 with ha_lt | ha_gt
  · have hab : a < b := H₂.lt_of_not_mem_of_lt_one haH₂ ha_lt hb
    have hba : b < a⁻¹ := H₂.lt_of_not_mem_of_one_lt hainv (one_lt_inv_of_inv ha_lt) hb
    exact H₁.convex haH₁ (inv_mem haH₁) hab.le hba.le
  · have hba : b < a := H₂.lt_of_not_mem_of_one_lt haH₂ ha_gt hb
    have hab : a⁻¹ < b := H₂.lt_of_not_mem_of_lt_one hainv (inv_lt_one_of_one_lt ha_gt) hb
    exact H₁.convex (inv_mem haH₁) haH₁ hab.le hba.le

noncomputable instance : LinearOrder (ConvexSubgroup Γ) :=
  { (inferInstance : PartialOrder (ConvexSubgroup Γ)) with
    le_total := le_total_of_convex
    toDecidableLE := Classical.decRel _
    toDecidableEq := Classical.decEq _
    toDecidableLT := Classical.decRel _ }

/-! ### The smallest convex subgroup containing a set -/

/-- The smallest convex subgroup containing a set `S`, as the intersection of all convex
subgroups containing `S`. This construction underwrites the convex subgroup `cΓ_v(I)` of
Wedhorn Definition 7.3. -/
def minContain (S : Set Γ) : ConvexSubgroup Γ where
  toSubgroup :=
    { carrier := {x | ∀ H : ConvexSubgroup Γ, S ⊆ H → x ∈ H}
      one_mem' := fun H _ ↦ one_mem H
      mul_mem' := fun ha hb H hS ↦ mul_mem (ha H hS) (hb H hS)
      inv_mem' := fun ha H hS ↦ inv_mem (ha H hS) }
  convex' := fun ha hb h₁ h₂ H hS ↦ H.convex (ha H hS) (hb H hS) h₁ h₂

omit [IsOrderedMonoid Γ] in
/-- The generating set is contained in the convex subgroup it generates. -/
theorem subset_minContain (S : Set Γ) : S ⊆ minContain S :=
  fun _ hx _ hS ↦ hS hx

omit [IsOrderedMonoid Γ] in
/-- Universal property: `minContain S` lies inside every convex subgroup containing `S`. -/
theorem minContain_le {S : Set Γ} {H : ConvexSubgroup Γ} (hS : S ⊆ H) : minContain S ≤ H :=
  fun _ hx ↦ hx H hS

/-! ### The largest convex subgroup avoiding an element -/

/-- The largest convex subgroup avoiding an element `γ ≠ 1`, as the union of all convex
subgroups excluding `γ` — a union which is directed because convex subgroups are totally
ordered. -/
noncomputable def maxAvoid {γ : Γ} (hγ : γ ≠ 1) : ConvexSubgroup Γ where
  toSubgroup :=
    { carrier := {x | ∃ H : ConvexSubgroup Γ, γ ∉ H ∧ x ∈ H}
      mul_mem' := fun {a b} ⟨H₁, hγ₁, ha⟩ ⟨H₂, hγ₂, hb⟩ ↦ by
        rcases le_total_of_convex H₁ H₂ with h | h
        · exact ⟨H₂, hγ₂, H₂.toSubgroup.mul_mem (h _ ha) hb⟩
        · exact ⟨H₁, hγ₁, H₁.toSubgroup.mul_mem ha (h _ hb)⟩
      one_mem' := ⟨⊥, mem_bot.not.mpr hγ, one_mem ⊥⟩
      inv_mem' := fun {a} ⟨H, hγH, ha⟩ ↦ ⟨H, hγH, H.toSubgroup.inv_mem ha⟩ }
  convex' := by
    rintro a b x ⟨H₁, hγ₁, ha⟩ ⟨H₂, hγ₂, hb⟩ h₁ h₂
    rcases le_total_of_convex H₁ H₂ with h | h
    · exact ⟨H₂, hγ₂, H₂.convex (h _ ha) hb h₁ h₂⟩
    · exact ⟨H₁, hγ₁, H₁.convex ha (h _ hb) h₁ h₂⟩

/-- Membership in `maxAvoid hγ`: some convex subgroup excludes `γ` but contains `x`. -/
theorem mem_maxAvoid_iff {γ : Γ} {hγ : γ ≠ 1} {x : Γ} :
    x ∈ maxAvoid hγ ↔ ∃ H : ConvexSubgroup Γ, γ ∉ H ∧ x ∈ H :=
  Iff.rfl

/-- The avoided element is not a member. -/
theorem not_mem_maxAvoid {γ : Γ} (hγ : γ ≠ 1) : γ ∉ maxAvoid hγ :=
  fun ⟨_, hγH, hγH'⟩ ↦ hγH hγH'

/-- Universal property: every convex subgroup excluding `γ` lies inside `maxAvoid hγ`. -/
theorem le_maxAvoid_of_not_mem {γ : Γ} {hγ : γ ≠ 1} {H : ConvexSubgroup Γ} (h : γ ∉ H) :
    H ≤ maxAvoid hγ :=
  fun _ hx ↦ ⟨H, h, hx⟩

/-! ### Preimages of convex subgroups -/

/-- The preimage of a convex subgroup under a monotone group homomorphism is a convex
subgroup. This lifts convex subgroups from quotient value groups back to the original
value group. -/
def comap {Δ : Type*} [CommGroup Δ] [LinearOrder Δ] [IsOrderedMonoid Δ]
    (K : ConvexSubgroup Δ) (f : Γ →* Δ) (hf : Monotone f) : ConvexSubgroup Γ where
  toSubgroup := K.toSubgroup.comap f
  convex' := fun ha hb hax hxb ↦ K.convex ha hb (hf hax) (hf hxb)

omit [IsOrderedMonoid Γ] in
@[simp]
theorem mem_comap {Δ : Type*} [CommGroup Δ] [LinearOrder Δ] [IsOrderedMonoid Δ]
    {K : ConvexSubgroup Δ} {f : Γ →* Δ} {hf : Monotone f} {x : Γ} :
    x ∈ K.comap f hf ↔ f x ∈ K :=
  Iff.rfl

end ConvexSubgroup

end TauCeti
