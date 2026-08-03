/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity
import Mathlib.Tactic.Group

/-!
# Hecke rings: commutativity via an anti-involution

Shimura's commutativity criterion (Proposition 3.8 of [Shimura][shimura1971]): if the group
`G` admits an anti-involution `ι` preserving both `H` and `Δ` and fixing every double coset
`HgH` for `g ∈ Δ`, then Shimura's multiplicity is symmetric, `m(g₁, g₂; d) = m(g₂, g₁; d)`,
so the structure constants of the convolution product are symmetric and the Hecke ring
`𝕋 Δ H R` is commutative for every commutative semiring `R`. The classical instance is the
transpose on `GL₂(ℚ)`, which fixes the double cosets of `M₂(ℤ)`-integral matrices by the
elementary divisor theorem.

The symmetry of the multiplicity is proved through the one-sided count
`DoubleCoset.multiplicity_eq_card_filter`: the anti-involution induces an injection between
the two count sets by transporting the representative decomposition of `(σᵢ g₁)⁻¹ d` through
`ι` (Shimura's change of variables), and the two opposite injections give equality.

Ported from the AINTLIB `LeanModularForms` project
(`HeckeRIngs/AbstractHeckeRing/Commutativity.lean`,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), per the
ModularForms roadmap's dependency policy, rebuilt on the one-sided multiplicity count of the
vendored Mathlib stack.

## Main definitions

* `HeckeAntiInvolution`: an anti-involution of `G` (a monoid homomorphism `G →* Gᵐᵒᵖ`,
  involutive on `G`) preserving `H` and `Δ`.
* `HeckeAntiInvolution.onHeckeCoset`: the induced action on double cosets.

## Main results

* `HeckeAntiInvolution.multiplicity_comm`: Shimura's multiplicity is symmetric when the
  anti-involution fixes every double coset.
* `HeckeCosetModule.mul_comm_of_antiInvolution`: the convolution product is commutative.
* `HeckeCosetModule.commSemiringOfAntiInvolution`: the resulting `CommSemiring (𝕋 Δ H R)`.
-/

public section

open DoubleCoset Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G}

/-- An anti-involution of the Hecke datum `(Δ, H)`: a monoid homomorphism `G →* Gᵐᵒᵖ`
(equivalently, an anti-homomorphism of `G`) that is involutive and preserves membership in
both `H` and `Δ`. Shimura's commutativity criterion applies when it moreover fixes every
double coset `HgH`, `g ∈ Δ`; see `HeckeAntiInvolution.multiplicity_comm`. -/
structure HeckeAntiInvolution (Δ : Submonoid G) (H : Subgroup G) where
  /-- The underlying homomorphism to the opposite group. -/
  toFun : G →* Gᵐᵒᵖ
  /-- The induced map on `G` is involutive. -/
  involutive : ∀ g, (toFun (toFun g).unop).unop = g
  /-- The induced map preserves membership in `H`. -/
  mem_H : ∀ g ∈ H, (toFun g).unop ∈ H
  /-- The induced map preserves membership in `Δ`. -/
  mem_Δ : ∀ g ∈ Δ, (toFun g).unop ∈ Δ

namespace HeckeAntiInvolution

variable (ι : HeckeAntiInvolution Δ H)

/-- The underlying function of the anti-involution, viewed as a map `G → G`. -/
def bar (g : G) : G := (ι.toFun g).unop

/-- The anti-involution is an involution. -/
@[simp] lemma bar_bar (g : G) : ι.bar (ι.bar g) = g := ι.involutive g

/-- The anti-involution reverses multiplication. -/
lemma bar_mul (a b : G) : ι.bar (a * b) = ι.bar b * ι.bar a := by simp [bar]

/-- The anti-involution commutes with inversion. -/
lemma bar_inv (g : G) : ι.bar g⁻¹ = (ι.bar g)⁻¹ := by simp [bar]

/-- The anti-involution preserves membership in `H`. -/
lemma bar_mem_H {g : G} (hg : g ∈ H) : ι.bar g ∈ H := ι.mem_H g hg

/-- The anti-involution preserves membership in `Δ`. -/
lemma bar_mem_Δ {g : G} (hg : g ∈ Δ) : ι.bar g ∈ Δ := ι.mem_Δ g hg

/-- The anti-involution maps the double coset of `a` into the double coset of `bar a`. -/
lemma bar_mem_doubleCoset {a x : G} (hx : x ∈ doubleCoset a (H : Set G) H) :
    ι.bar x ∈ doubleCoset (ι.bar a) (H : Set G) H := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_doubleCoset.mp hx
  exact mem_doubleCoset.mpr ⟨ι.bar h₂, ι.bar_mem_H hh₂, ι.bar h₁, ι.bar_mem_H hh₁, by
    rw [ι.bar_mul, ι.bar_mul, mul_assoc]⟩

/-- The induced action of the anti-involution on the double cosets `H\Δ/H`. -/
noncomputable def onHeckeCoset (D : HeckeCoset Δ H H) : HeckeCoset Δ H H :=
  HeckeCoset.mk H H ⟨ι.bar (D.rep : G), ι.bar_mem_Δ D.rep.2⟩

/-- `onHeckeCoset` sends the class of `g` to the class of `bar g`. -/
lemma onHeckeCoset_mk (g : Δ) :
    ι.onHeckeCoset (HeckeCoset.mk H H g) =
      HeckeCoset.mk H H ⟨ι.bar (g : G), ι.bar_mem_Δ g.2⟩ := by
  refine HeckeCoset.eq_iff.mpr ?_
  have hrep : ((HeckeCoset.mk H H g).rep : G) ∈ doubleCoset (g : G) (H : Set G) H := by
    have h := HeckeCoset.rep_mem (HeckeCoset.mk H H g)
    rwa [HeckeCoset.toSet_mk] at h
  exact doubleCoset_eq_of_mem (ι.bar_mem_doubleCoset hrep)

/-- When the anti-involution fixes every double coset, `bar g` lies in the double coset of
`g` for every `g ∈ Δ`. -/
lemma bar_mem_doubleCoset_self (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D)
    (g : Δ) : ι.bar (g : G) ∈ doubleCoset (g : G) (H : Set G) H := by
  have hg := congrArg HeckeCoset.toSet ((ι.onHeckeCoset_mk g).symm.trans (h_fix _))
  rw [HeckeCoset.toSet_mk, HeckeCoset.toSet_mk] at hg
  exact hg ▸ mem_doubleCoset_self H H _

/-- Decompose `bar x` through the double coset of `g` when `x ∈ HgH`. -/
lemma exists_bar_eq (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D)
    {g : Δ} {x : G} (hx : x ∈ doubleCoset (g : G) (H : Set G) H) :
    ∃ a ∈ H, ∃ b ∈ H, ι.bar x = a * (g : G) * b := by
  have hbar := ι.bar_mem_doubleCoset hx
  rw [doubleCoset_eq_of_mem (ι.bar_mem_doubleCoset_self h_fix g)] at hbar
  exact mem_doubleCoset.mp hbar

/-- The conjugation criterion for the stabilizer subgroup indexing `DecompQuotient`: an
element `n` of the stabilizer conjugates into `H` under `g`. -/
private lemma conj_mem_of_stabilizer (g : G)
    (n : (ConjAct.toConjAct g • H).subgroupOf H) : g⁻¹ * (n : G) * g ∈ H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simpa [ConjAct.ofConjAct_toConjAct] using hn

/-- Equality of classes in `DecompQuotient H H g` yields the conjugation relation of their
representatives. -/
private lemma conj_mem_of_mk_eq (g : G) {u₁ u₂ : H}
    (h : (QuotientGroup.mk u₁ : DecompQuotient H H g) = QuotientGroup.mk u₂) :
    g⁻¹ * ((u₁ : G)⁻¹ * u₂) * g ∈ H := by
  have hk := QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, inv_inv] at hk
  simpa [mul_assoc] using hk

/-- Membership in the one-sided count set is invariant under replacing a representative of
a class in `DecompQuotient H H g₂` by the canonical `out`. -/
private lemma out_mul_inv_mul_mem {g₁ g₂ d : G} {u : G} (hu : u ∈ H)
    (hmem : (u * g₂)⁻¹ * d ∈ doubleCoset g₁ (H : Set G) H) :
    ((((QuotientGroup.mk ⟨u, hu⟩ : DecompQuotient H H g₂).out : G)) * g₂)⁻¹ * d ∈
      doubleCoset g₁ (H : Set G) H := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct g₂ • H).subgroupOf H) (⟨u, hu⟩ : H)
  have hout : (((QuotientGroup.mk ⟨u, hu⟩ : DecompQuotient H H g₂).out : G)) = u * n := by
    simpa [Subgroup.coe_mul] using congrArg (Subtype.val : H → G) hn
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := mem_doubleCoset.mp hmem
  refine mem_doubleCoset.mpr ⟨g₂⁻¹ * (n : G)⁻¹ * g₂ * h₁,
    H.mul_mem (by simpa [mul_assoc] using H.inv_mem (conj_mem_of_stabilizer g₂ n)) hh₁,
    h₂, hh₂, ?_⟩
  rw [hout]
  calc (u * n * g₂)⁻¹ * d
      = (g₂⁻¹ * (n : G)⁻¹ * g₂) * ((u * g₂)⁻¹ * d) := by group
    _ = (g₂⁻¹ * (n : G)⁻¹ * g₂) * (h₁ * g₁ * h₂) := by rw [heq]
    _ = g₂⁻¹ * (n : G)⁻¹ * g₂ * h₁ * g₁ * h₂ := by group

open Classical in
/-- Shimura's change of variables: the anti-involution transports a member of the one-sided
count set of `m(g₁, g₂; d)` to a member of the one-sided count set of `m(g₂, g₁; d)`. -/
private noncomputable def commFwdMap (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D)
    (g₁ g₂ d : Δ) {aD bD : G} (haD : aD ∈ H) (hbD : bD ∈ H)
    (hbarD : ι.bar (d : G) = aD * (d : G) * bD)
    {a₁ b₁ : G} (ha₁ : a₁ ∈ H) (hb₁ : b₁ ∈ H)
    (hbar₁ : ι.bar (g₁ : G) = a₁ * (g₁ : G) * b₁)
    (p : {i : DecompQuotient H H (g₁ : G) |
      ((i.out : G) * g₁)⁻¹ * (d : G) ∈ doubleCoset (g₂ : G) (H : Set G) H}) :
    {j : DecompQuotient H H (g₂ : G) |
      ((j.out : G) * g₂)⁻¹ * (d : G) ∈ doubleCoset (g₁ : G) (H : Set G) H} :=
  have hx : ∃ a ∈ H, ∃ b ∈ H,
      ι.bar (((p.1.out : G) * g₁)⁻¹ * (d : G)) = a * (g₂ : G) * b :=
    ι.exists_bar_eq h_fix p.2
  ⟨QuotientGroup.mk ⟨aD⁻¹ * hx.choose, H.mul_mem (H.inv_mem haD) hx.choose_spec.1⟩,
    out_mul_inv_mul_mem _ (by
      -- the raw membership `((aD⁻¹ * a * g₂)⁻¹ * d ∈ H g₁ H` for the chosen decomposition
      -- `bar((σᵢ g₁)⁻¹ d) = a g₂ b`, before passing to the canonical representative
      obtain ⟨hb, hbar⟩ := hx.choose_spec.2.choose_spec
      set a := hx.choose
      set b := hx.choose_spec.2.choose
      have hd : (d : G) = (p.1.out : G) * (g₁ : G) * (((p.1.out : G) * g₁)⁻¹ * (d : G)) := by
        group
      have h2 : ι.bar ((p.1.out : G) * (g₁ : G) * (((p.1.out : G) * g₁)⁻¹ * (d : G))) =
          ι.bar (((p.1.out : G) * g₁)⁻¹ * (d : G)) *
            (ι.bar (g₁ : G) * ι.bar (p.1.out : G)) := by
        rw [ι.bar_mul ((p.1.out : G) * (g₁ : G)), ι.bar_mul (p.1.out : G)]
      have hkey : aD * (d : G) * bD =
          a * (g₂ : G) * b * (a₁ * (g₁ : G) * b₁) * ι.bar (p.1.out : G) := by
        rw [← hbarD, ← hbar, ← hbar₁]
        conv_lhs => rw [hd]
        rw [h2]
        group
      refine mem_doubleCoset.mpr ⟨b * a₁, H.mul_mem hb ha₁,
        b₁ * ι.bar (p.1.out : G) * bD⁻¹,
        H.mul_mem (H.mul_mem hb₁ (ι.bar_mem_H (p.1.out : H).2)) (H.inv_mem hbD), ?_⟩
      have hADd : aD * (d : G) =
          a * (g₂ : G) * (b * a₁ * (g₁ : G) * (b₁ * ι.bar (p.1.out : G) * bD⁻¹)) := by
        calc aD * (d : G) = aD * (d : G) * bD * bD⁻¹ := by group
          _ = a * (g₂ : G) * b * (a₁ * (g₁ : G) * b₁) * ι.bar (p.1.out : G) * bD⁻¹ := by
            rw [hkey]
          _ = a * (g₂ : G) * (b * a₁ * (g₁ : G) * (b₁ * ι.bar (p.1.out : G) * bD⁻¹)) := by
            group
      calc (aD⁻¹ * a * (g₂ : G))⁻¹ * (d : G)
          = ((g₂ : G))⁻¹ * a⁻¹ * (aD * (d : G)) := by group
        _ = ((g₂ : G))⁻¹ * a⁻¹ *
              (a * (g₂ : G) * (b * a₁ * (g₁ : G) * (b₁ * ι.bar (p.1.out : G) * bD⁻¹))) := by
            rw [hADd]
        _ = b * a₁ * (g₁ : G) * (b₁ * ι.bar (p.1.out : G) * bD⁻¹) := by group)⟩

/-- Transport back through the anti-involution: two elements whose barred decompositions
share the middle `g₂` with stabilizer-related left parts differ by an element of `H`. -/
private lemma bar_diff_mem {x₁ x₂ g₂ : G} {a₁' b₁' a₂' b₂' : G}
    (hb₁' : b₁' ∈ H) (hb₂' : b₂' ∈ H)
    (hbar₁' : ι.bar x₁ = a₁' * g₂ * b₁') (hbar₂' : ι.bar x₂ = a₂' * g₂ * b₂')
    (hconj : g₂⁻¹ * (a₁'⁻¹ * a₂') * g₂ ∈ H) : x₂ * x₁⁻¹ ∈ H := by
  have hcalc : ι.bar (x₂ * x₁⁻¹) = b₁'⁻¹ * (g₂⁻¹ * (a₁'⁻¹ * a₂') * g₂) * b₂' := by
    rw [ι.bar_mul, ι.bar_inv, hbar₁', hbar₂']
    group
  have hmem : ι.bar (x₂ * x₁⁻¹) ∈ H :=
    hcalc ▸ H.mul_mem (H.mul_mem (H.inv_mem hb₁') hconj) hb₂'
  have hbb := ι.bar_mem_H hmem
  rwa [ι.bar_bar] at hbb

/-- The transported class determines the original: two members of the count set with barred
decompositions sharing the middle `g₂` and stabilizer-related left parts differ by `H` on
the left of `g₁`. -/
private lemma commFwdMap_injective
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D)
    (g₁ g₂ d : Δ) {aD bD : G} (haD : aD ∈ H) (hbD : bD ∈ H)
    (hbarD : ι.bar (d : G) = aD * (d : G) * bD)
    {a₁ b₁ : G} (ha₁ : a₁ ∈ H) (hb₁ : b₁ ∈ H)
    (hbar₁ : ι.bar (g₁ : G) = a₁ * (g₁ : G) * b₁) :
    Function.Injective (ι.commFwdMap h_fix g₁ g₂ d haD hbD hbarD ha₁ hb₁ hbar₁) := by
  intro p₁ p₂ heq
  have hx₁ : ∃ a ∈ H, ∃ b ∈ H,
      ι.bar (((p₁.1.out : G) * g₁)⁻¹ * (d : G)) = a * (g₂ : G) * b :=
    ι.exists_bar_eq h_fix p₁.2
  have hx₂ : ∃ a ∈ H, ∃ b ∈ H,
      ι.bar (((p₂.1.out : G) * g₁)⁻¹ * (d : G)) = a * (g₂ : G) * b :=
    ι.exists_bar_eq h_fix p₂.2
  have hmk : (QuotientGroup.mk ⟨aD⁻¹ * hx₁.choose,
        H.mul_mem (H.inv_mem haD) hx₁.choose_spec.1⟩ : DecompQuotient H H (g₂ : G)) =
      QuotientGroup.mk ⟨aD⁻¹ * hx₂.choose,
        H.mul_mem (H.inv_mem haD) hx₂.choose_spec.1⟩ :=
    congrArg Subtype.val heq
  have hconj := conj_mem_of_mk_eq (g₂ : G) hmk
  -- the conjugation relation transfers to the chosen left parts, since `aD` cancels
  have hconj' : ((g₂ : G))⁻¹ * (hx₁.choose⁻¹ * hx₂.choose) * g₂ ∈ H := by
    simpa [mul_assoc] using hconj
  -- transport back through the anti-involution: the two count-set elements differ by `H`
  have hdiff : (((p₂.1.out : G) * g₁)⁻¹ * (d : G)) *
      ((((p₁.1.out : G) * g₁)⁻¹ * (d : G)))⁻¹ ∈ H :=
    ι.bar_diff_mem hx₁.choose_spec.2.choose_spec.1 hx₂.choose_spec.2.choose_spec.1
      hx₁.choose_spec.2.choose_spec.2 hx₂.choose_spec.2.choose_spec.2 hconj'
  -- conclude equality in the decomposition quotient through the coset injectivity
  have hcoset : (((p₂.1.out : G) * g₁ : G) : G ⧸ H) = (((p₁.1.out : G) * g₁ : G) : G ⧸ H) := by
    rw [QuotientGroup.eq]
    have : (((p₂.1.out : G) * g₁)⁻¹ * (d : G)) *
        ((((p₁.1.out : G) * g₁)⁻¹ * (d : G)))⁻¹ =
        ((p₂.1.out : G) * g₁)⁻¹ * ((p₁.1.out : G) * g₁) := by group
    exact this ▸ hdiff
  exact Subtype.ext (mk_out_mul_injective H H (g₁ : G) hcoset.symm)

/-- One direction of the symmetry of Shimura's multiplicity under an anti-involution fixing
every double coset. -/
private lemma multiplicity_le_comm [IsHeckeTriple Δ H H]
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) (g₁ g₂ d : Δ) :
    multiplicity H H H (g₁ : G) (g₂ : G) (d : G) ≤
      multiplicity H H H (g₂ : G) (g₁ : G) (d : G) := by
  classical
  obtain ⟨aD, haD, bD, hbD, hbarD⟩ :=
    ι.exists_bar_eq h_fix (mem_doubleCoset_self H H (d : G))
  obtain ⟨a₁, ha₁, b₁, hb₁, hbar₁⟩ :=
    ι.exists_bar_eq h_fix (mem_doubleCoset_self H H (g₁ : G))
  rw [multiplicity_eq_card_filter, multiplicity_eq_card_filter]
  exact Nat.card_le_card_of_injective
    (ι.commFwdMap h_fix g₁ g₂ d haD hbD hbarD ha₁ hb₁ hbar₁)
    (ι.commFwdMap_injective h_fix g₁ g₂ d haD hbD hbarD ha₁ hb₁ hbar₁)

/-- **Shimura's multiplicity is symmetric under an anti-involution** (Proposition 3.8 of
[Shimura][shimura1971]): when the anti-involution fixes every double coset,
`m(g₁, g₂; d) = m(g₂, g₁; d)`. -/
theorem multiplicity_comm [IsHeckeTriple Δ H H]
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) (g₁ g₂ d : Δ) :
    multiplicity H H H (g₁ : G) (g₂ : G) (d : G) =
      multiplicity H H H (g₂ : G) (g₁ : G) (d : G) :=
  le_antisymm (ι.multiplicity_le_comm h_fix g₁ g₂ d) (ι.multiplicity_le_comm h_fix g₂ g₁ d)

end HeckeAntiInvolution

namespace HeckeCosetModule

open HeckeAntiInvolution

variable (R : Type*) {Δ : Submonoid G} {H : Subgroup G} [IsHeckeTriple Δ H H]

/-- The structure constants of the Hecke ring are symmetric under an anti-involution fixing
every double coset. -/
lemma structureConstants_comm [Semiring R] (ι : HeckeAntiInvolution Δ H)
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) (g₁ g₂ : Δ) :
    structureConstants R H H H g₁ g₂ = structureConstants R H H H g₂ g₁ := by
  classical
  ext D
  rw [structureConstants_apply, structureConstants_apply,
    ι.multiplicity_comm h_fix g₁ g₂ D.rep]

/-- **Shimura's commutativity criterion** (Proposition 3.8 of [Shimura][shimura1971]): the
Hecke ring over a commutative semiring is commutative when an anti-involution fixes every
double coset. -/
theorem mul_comm_of_antiInvolution [CommSemiring R] (ι : HeckeAntiInvolution Δ H)
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) (f g : 𝕋 Δ H R) :
    f * g = g * f := by
  induction f using HeckeCosetModule.induction_linear with
  | h0 => rw [mul_def, mul_def, HeckeCosetModule.zero_mul, HeckeCosetModule.mul_zero]
  | hadd f₁ f₂ h₁ h₂ => rw [_root_.add_mul, _root_.mul_add, h₁, h₂]
  | hsingle D₁ a =>
    induction g using HeckeCosetModule.induction_linear with
    | h0 => rw [mul_def, mul_def, HeckeCosetModule.zero_mul, HeckeCosetModule.mul_zero]
    | hadd g₁ g₂ h₁ h₂ => rw [_root_.mul_add, _root_.add_mul, h₁, h₂]
    | hsingle D₂ b =>
      rw [single_mul_single, single_mul_single,
        structureConstants_comm R ι h_fix D₂.rep D₁.rep, smul_comm]

/-- The Hecke ring over a commutative semiring is a commutative semiring when an
anti-involution fixes every double coset (Proposition 3.8 of [Shimura][shimura1971]). Not an
instance: the anti-involution is data supplied per application (for `GL₂` it is the
transpose). -/
@[instance_reducible]
noncomputable def commSemiringOfAntiInvolution [CommSemiring R] (ι : HeckeAntiInvolution Δ H)
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) : CommSemiring (𝕋 Δ H R) :=
  { instSemiringHeckeRing R with
    mul_comm := mul_comm_of_antiInvolution R ι h_fix }

end HeckeCosetModule
