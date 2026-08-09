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
  (`subgroupOf_conjAct_smul_mul_left_of_mem_normalizer`).

Ported from the AINTLIB [`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) project,
`LeanModularForms/HeckeRIngs/AbstractHeckeRing/StabConjugation.lean`
(Chris Birkbeck). The source states these for a bundled `HeckePair` and for `g` in the
ambient submonoid `Δ`; neither is used by the arguments, which are facts about conjugation
of subgroups, so they are stated here for arbitrary subgroups and an arbitrary `g : G`.

## Main results

* `DoubleCoset.conjAct_smul_mul_right_of_mem_normalizer`: `(gh)Γ(gh)⁻¹ = gΓg⁻¹` whenever `h`
  normalizes `Γ`.
* `DoubleCoset.subgroupOf_conjAct_smul_mul_left_of_mem_normalizer`: left multiplication by `h ∈ Γ₁`
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

/-- Left multiplication of the base point by anything normalizing `Γ₁` conjugates the
stabilizer by it: `x` stabilizes `hg` exactly when `h⁻¹xh` stabilizes `g`. Membership in `Γ₁`
itself is the special case `Subgroup.le_normalizer`.

The conjugating automorphism of `↥Γ₁` is `Subgroup.normalizerMonoidHom`, which is defined for
exactly this: `MulAut.conj h` would need `h` to be an element of `Γ₁`. -/
lemma subgroupOf_conjAct_smul_mul_left_of_mem_normalizer (Γ₁ Γ₂ : Subgroup G) (g : G)
    (h : Subgroup.normalizer (Γ₁ : Set G)) :
    (ConjAct.toConjAct ((h : G) * g) • Γ₂).subgroupOf Γ₁ =
      ((ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁).map
        (Γ₁.normalizerMonoidHom h).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
    Subgroup.normalizerMonoidHom_apply_symm_apply_coe]
  -- Both sides are membership of the *same* element of `Γ₂`, written with different
  -- bracketing: `(hg)⁻¹x(hg)` versus `g⁻¹(h⁻¹xh)g`. `group` proves that identity; the `iff`
  -- is then congruence along it, so no rewriting has to find a redex.
  exact iff_of_eq (congrArg (· ∈ Γ₂) (by group))

/-- Moving the base point on the left by anything normalizing `Γ₁` is an equivalence of
decomposition quotients, `Γ₁/Stab(hg) ≃ Γ₁/Stab(g)`, induced by `σ ↦ h⁻¹σh`.

Well-definedness is `subgroupOf_conjAct_smul_mul_left_of_mem_normalizer`: the two stabilizers
differ by that conjugation, so it carries one coset relation to the other. -/
noncomputable def decompQuotientEquivMulLeft (Γ₁ Γ₂ : Subgroup G) (g : G)
    (h : Subgroup.normalizer (Γ₁ : Set G)) :
    DecompQuotient Γ₁ Γ₂ ((h : G) * g) ≃ DecompQuotient Γ₁ Γ₂ g :=
  (Subgroup.quotientEquivOfEq
      (subgroupOf_conjAct_smul_mul_left_of_mem_normalizer Γ₁ Γ₂ g h)).trans <|
    Quotient.congr (Γ₁.normalizerMonoidHom h).symm.toEquiv fun a b ↦ by
      simp only [QuotientGroup.leftRel_apply, Subgroup.mem_map_equiv,
        MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_inv, ← map_mul]

/-- What `decompQuotientEquivMulLeft` does to a representative: it conjugates by `h⁻¹`.

Deliberately *not* `@[simp]`. The left-hand side is not in simp normal form and cannot be
made so: `QuotientGroup.mk`'s implicit subgroup argument comes from the type index
`DecompQuotient Γ₁ Γ₂ (↑h * g)`, and simp rewrites `ConjAct.toConjAct (↑h * g)` inside it to
`ConjAct.toConjAct ↑h * ConjAct.toConjAct g` via `ConjAct.toConjAct_mul`. `scripts/lint-env.sh`
reports exactly that as a `simpNF` violation. Rewrite with this lemma by name. -/
lemma decompQuotientEquivMulLeft_mk (Γ₁ Γ₂ : Subgroup G) (g : G)
    (h : Subgroup.normalizer (Γ₁ : Set G)) (x : Γ₁) :
    decompQuotientEquivMulLeft Γ₁ Γ₂ g h (QuotientGroup.mk x) =
      QuotientGroup.mk ((Γ₁.normalizerMonoidHom h).symm x) :=
  -- `(rfl)` rather than `rfl`: the equivalences are not `@[expose]`, so the parentheses opt
  -- out of exporting the definitional equality that this lemma exists to replace.
  (rfl)

/-- Moving the base point on both sides — on the left by anything normalizing `Γ₁`, on the
right by anything normalizing `Γ₂` — is again an equivalence of decomposition quotients. Right
multiplication contributes nothing (`subgroupOf_conjAct_smul_mul_right_of_mem_normalizer`), so
this is `decompQuotientEquivMulLeft` after re-associating. -/
noncomputable def decompQuotientEquivMulLeftRight (Γ₁ Γ₂ : Subgroup G) (g : G)
    (h : Subgroup.normalizer (Γ₁ : Set G)) {k : G} (hk : k ∈ Subgroup.normalizer Γ₂) :
    DecompQuotient Γ₁ Γ₂ ((h : G) * g * k) ≃ DecompQuotient Γ₁ Γ₂ g :=
  (Subgroup.quotientEquivOfEq (by rw [mul_assoc])).trans
    ((decompQuotientEquivMulLeft Γ₁ Γ₂ (g * k) h).trans
      (Subgroup.quotientEquivOfEq
        (subgroupOf_conjAct_smul_mul_right_of_mem_normalizer Γ₁ Γ₂ g hk)))

/-- What `decompQuotientEquivMulLeftRight` does to a representative. Not `@[simp]`, for the
same reason as `decompQuotientEquivMulLeft_mk`. -/
lemma decompQuotientEquivMulLeftRight_mk (Γ₁ Γ₂ : Subgroup G) (g : G)
    (h : Subgroup.normalizer (Γ₁ : Set G)) {k : G} (hk : k ∈ Subgroup.normalizer Γ₂) (x : Γ₁) :
    decompQuotientEquivMulLeftRight Γ₁ Γ₂ g h hk (QuotientGroup.mk x) =
      QuotientGroup.mk ((Γ₁.normalizerMonoidHom h).symm x) :=
  (rfl)

end DoubleCoset
