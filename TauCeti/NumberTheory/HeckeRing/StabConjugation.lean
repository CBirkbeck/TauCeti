/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Basic

import Mathlib.Tactic.Group

/-!
# Moving the base point of a decomposition quotient

`DoubleCoset.DecompQuotient Γ₁ Γ₂ g` is `Γ₁ ⧸ (gΓ₂g⁻¹).subgroupOf Γ₁`, so it depends on `g`
only through the conjugate `gΓ₂g⁻¹`. This file records how that conjugate — and hence the
quotient — responds to multiplying `g` on either side by a group element:

* multiplying on the **right** by anything normalizing `Γ₂` changes nothing at all, since
  `(gh)Γ₂(gh)⁻¹ = gΓ₂g⁻¹` (`conjAct_smul_mul_right_of_mem_normalizer`,
  `subgroupOf_conjAct_smul_mul_right_of_mem_normalizer`);
* multiplying on the **left** by `h ∈ Γ₁` conjugates the stabilizer by `h`
  (`subgroupOf_conjAct_smul_mul_left_of_mem`).

Ported from the AINTLIB [`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) project,
`LeanModularForms/HeckeRIngs/AbstractHeckeRing/StabConjugation.lean`
(Chris Birkbeck). The source states these for a bundled `HeckePair` and for `g` in the
ambient submonoid `Δ`; neither is used by the arguments, which are facts about conjugation
of subgroups, so they are stated here for arbitrary subgroups and an arbitrary `g : G`.

## Main results

* `DoubleCoset.conjAct_smul_mul_right_of_mem_normalizer`: `(gh)Γ(gh)⁻¹ = gΓg⁻¹` whenever `h`
  normalizes `Γ`.
* `DoubleCoset.subgroupOf_conjAct_smul_mul_left_of_mem`: left multiplication by `h ∈ Γ₁`
  conjugates the stabilizer by `h`.
* `DoubleCoset.decompQuotientEquivMulLeft`, `DoubleCoset.decompQuotientEquivMulLeftRight`:
  the induced equivalences of decomposition quotients.
-/

public section

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G]

/-- Conjugation only sees `g` modulo the normalizer on the right: `(gh)Γ(gh)⁻¹ = gΓg⁻¹`
whenever `h` normalizes `Γ`. Membership in `Γ` itself is the special case
`Subgroup.le_normalizer`. -/
lemma conjAct_smul_mul_right_of_mem_normalizer (Γ : Subgroup G) (g : G) {h : G}
    (hh : h ∈ Subgroup.normalizer Γ) :
    ConjAct.toConjAct (g * h) • Γ = ConjAct.toConjAct g • Γ := by
  rw [map_mul, ← smul_smul, Subgroup.conjAct_pointwise_smul_eq_self hh]

/-- The stabilizer cut out inside `Γ₁` is unchanged by right multiplication of the base point
by anything normalizing `Γ₂`. -/
lemma subgroupOf_conjAct_smul_mul_right_of_mem_normalizer (Γ₁ Γ₂ : Subgroup G) (g : G) {h : G}
    (hh : h ∈ Subgroup.normalizer Γ₂) :
    (ConjAct.toConjAct (g * h) • Γ₂).subgroupOf Γ₁ =
      (ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁ := by
  rw [conjAct_smul_mul_right_of_mem_normalizer Γ₂ g hh]

/-- Left multiplication of the base point by `h ∈ Γ₁` conjugates the stabilizer by `h`:
`x` stabilizes `hg` exactly when `h⁻¹xh` stabilizes `g`. -/
lemma subgroupOf_conjAct_smul_mul_left_of_mem (Γ₁ Γ₂ : Subgroup G) (g : G) (h : Γ₁) :
    (ConjAct.toConjAct ((h : G) * g) • Γ₂).subgroupOf Γ₁ =
      ((ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁).map (MulAut.conj h).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  -- Both directions produce a membership stated about a `↥Γ₁` element whose value is a
  -- product; `change` names the underlying `G`-element so `group` can normalise it. The
  -- `Subgroup.mem_subgroupOf` simp step above leaves the coercion implicit, which is what
  -- makes the explicit form necessary rather than merely convenient.
  constructor
  · intro hx
    refine ⟨⟨(h : G)⁻¹ * (x : G) * (h : G),
      Γ₁.mul_mem (Γ₁.mul_mem (Γ₁.inv_mem h.2) x.2) h.2⟩, ?_, ?_⟩
    · change (g : G)⁻¹ * ((h : G)⁻¹ * (x : G) * (h : G)) * g ∈ Γ₂
      rw [show (g : G)⁻¹ * ((h : G)⁻¹ * (x : G) * (h : G)) * g =
        ((h : G) * g)⁻¹ * (x : G) * ((h : G) * g) by group]
      exact hx
    · -- the witness conjugates back to `x`; check it on underlying elements
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  · rintro ⟨y, hy, rfl⟩
    change ((h : G) * g)⁻¹ * ((h : G) * (y : G) * (h : G)⁻¹) * ((h : G) * g) ∈ Γ₂
    rw [show ((h : G) * g)⁻¹ * ((h : G) * (y : G) * (h : G)⁻¹) * ((h : G) * g) =
      g⁻¹ * (y : G) * g by group]
    exact hy

/-- Moving the base point by `h ∈ Γ₁` on the left is an equivalence of decomposition
quotients, `Γ₁/Stab(hg) ≃ Γ₁/Stab(g)`, induced by `σ ↦ h⁻¹σh`.

Well-definedness is `subgroupOf_conjAct_smul_mul_left_of_mem`: the two stabilizers differ by
conjugation by `h`, so that conjugation carries one coset relation to the other. -/
noncomputable def decompQuotientEquivMulLeft (Γ₁ Γ₂ : Subgroup G) (g : G) (h : Γ₁) :
    DecompQuotient Γ₁ Γ₂ ((h : G) * g) ≃ DecompQuotient Γ₁ Γ₂ g :=
  (Subgroup.quotientEquivOfEq (subgroupOf_conjAct_smul_mul_left_of_mem Γ₁ Γ₂ g h)).trans <|
    Quotient.congr (MulAut.conj h).symm.toEquiv fun a b ↦ by
      simp only [QuotientGroup.leftRel_apply, Subgroup.mem_map_equiv,
        MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_inv, ← map_mul]

@[simp]
lemma decompQuotientEquivMulLeft_mk (Γ₁ Γ₂ : Subgroup G) (g : G) (h : Γ₁) (x : Γ₁) :
    decompQuotientEquivMulLeft Γ₁ Γ₂ g h (QuotientGroup.mk x) =
      QuotientGroup.mk ((MulAut.conj h).symm x) :=
  -- `(rfl)` rather than `rfl`: the equivalences are not `@[expose]`, so the parentheses opt
  -- out of exporting the definitional equality that this lemma exists to replace.
  (rfl)

/-- Moving the base point on both sides — by `h ∈ Γ₁` on the left and by anything normalizing
`Γ₂` on the right — is again an equivalence of decomposition quotients. Right multiplication
contributes nothing (`subgroupOf_conjAct_smul_mul_right_of_mem_normalizer`), so this is
`decompQuotientEquivMulLeft` after re-associating. -/
noncomputable def decompQuotientEquivMulLeftRight (Γ₁ Γ₂ : Subgroup G) (g : G) (h : Γ₁)
    {k : G} (hk : k ∈ Subgroup.normalizer Γ₂) :
    DecompQuotient Γ₁ Γ₂ ((h : G) * g * k) ≃ DecompQuotient Γ₁ Γ₂ g :=
  (Subgroup.quotientEquivOfEq (by rw [mul_assoc])).trans
    ((decompQuotientEquivMulLeft Γ₁ Γ₂ (g * k) h).trans
      (Subgroup.quotientEquivOfEq
        (subgroupOf_conjAct_smul_mul_right_of_mem_normalizer Γ₁ Γ₂ g hk)))

@[simp]
lemma decompQuotientEquivMulLeftRight_mk (Γ₁ Γ₂ : Subgroup G) (g : G) (h : Γ₁) {k : G}
    (hk : k ∈ Subgroup.normalizer Γ₂) (x : Γ₁) :
    decompQuotientEquivMulLeftRight Γ₁ Γ₂ g h hk (QuotientGroup.mk x) =
      QuotientGroup.mk ((MulAut.conj h).symm x) :=
  -- `(rfl)` rather than `rfl`: the equivalences are not `@[expose]`, so the parentheses opt
  -- out of exporting the definitional equality that this lemma exists to replace.
  (rfl)

end DoubleCoset
