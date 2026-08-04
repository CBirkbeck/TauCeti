/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import TauCeti.NumberTheory.HeckeRing.Multiplication
import Mathlib.Tactic.Group

/-!
# Hecke rings: the module of left cosets

The scalar operations underlying the natural representation of the Hecke ring, following
[Shimura][shimura1971], §3.1: on the free module `HeckeCoset Δ ⊥ H →₀ R` over the left
cosets `Δ/H`, each element of `𝕋 Δ H R` defines a scalar operation, with a double coset
`HgH = ⊔ᵢ σᵢgH` sending a left coset `βH` to `Σᵢ βσᵢgH`. This file constructs the
left-coset type, the orbit Finsets, and the scalar multiplication, and proves it is
additive in both arguments and faithful. The action laws proper — compatibility with the
convolution product and its identity, which upgrade these operations to a module structure —
are Shimura's Proposition 3.2 and are established together with the degree homomorphism in
the follow-up development.

Ported from the AINTLIB `LeanModularForms` project
(`HeckeRIngs/AbstractHeckeRing/Module.lean`,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), per the
ModularForms roadmap's dependency policy, rebuilt on the left-coset quotient of the vendored
Mathlib stack.

## Main definitions

* `HeckeCoset.mk_bot_eq_mk_bot`: the left cosets of `H` with a representative in `Δ` are
  the bottom-left double cosets `HeckeCoset Δ ⊥ H` (`⊥βH = βH`); this characterization makes
  the existing double-coset quotient serve as the left-coset quotient, with no new type.
* `HeckeCoset.smulOrbit H g β`: the orbit Finset `{βσᵢgH}` of a left coset under a
  double coset representative.
* the `SMul (𝕋 Δ H R) (HeckeCoset Δ ⊥ H →₀ R)` instance.

## Main results

* `HeckeCoset.smulOrbit_congr`, `HeckeCoset.smulOrbit_disjoint`: the orbit depends
  only on the left coset, and orbits of distinct double cosets are disjoint.
* `HeckeLeftCosetModule.instFaithfulSMul`: the action of the Hecke ring on the module of
  left cosets is faithful.
-/

public section

open DoubleCoset Subgroup

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G}

/-!
The left cosets `βH` of `Δ`-elements are the bottom-left specialization `HeckeCoset Δ ⊥ H`
of the double cosets: `⊥βH = βH`. The type, constructor `HeckeCoset.mk ⊥ H`,
representative `HeckeCoset.rep`, and induction principle are all reused from the
double-coset API (they are built from the data alone); this section adds only the
`⊥`-specialized characterizations.
-/

namespace HeckeCoset

variable (Δ) in
/-- The identity left coset `1H = H` in the bottom-left specialization. -/
instance : One (HeckeCoset Δ ⊥ H) := ⟨mk ⊥ H ⟨1, Δ.one_mem⟩⟩

lemma bot_one_def : (1 : HeckeCoset Δ ⊥ H) = mk ⊥ H ⟨1, Δ.one_mem⟩ := (rfl)

/-- In the bottom-left specialization two elements define the same class iff they differ by
an element of `H` on the right: `⊥β₁H = ⊥β₂H ↔ β₁H = β₂H`. This is the entry point through
which the double-coset quotient serves as the left-coset quotient. -/
lemma mk_bot_eq_mk_bot {β₁ β₂ : Δ} :
    mk ⊥ H β₁ = mk ⊥ H β₂ ↔ ((β₁ : G))⁻¹ * (β₂ : G) ∈ H := by
  rw [eq_iff]
  constructor
  · intro h
    have hmem : (β₂ : G) ∈ doubleCoset (β₁ : G) ((⊥ : Subgroup G) : Set G) H :=
      h ▸ mem_doubleCoset_self _ _ _
    obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := mem_doubleCoset.mp hmem
    obtain rfl : h₁ = 1 := hh₁
    rw [heq]
    simpa using hh₂
  · intro h
    exact doubleCoset_eq_of_mem (mem_doubleCoset.mpr
      ⟨1, Subgroup.mem_bot.mpr rfl, (β₂ : G)⁻¹ * (β₁ : G),
        by simpa using H.inv_mem h, by group⟩)

/-- The representative of the class of `β` differs from `β` by an element of `H`. -/
lemma inv_rep_mul_mem (β : Δ) : (((mk ⊥ H β : HeckeCoset Δ ⊥ H).rep : G))⁻¹ * (β : G) ∈ H :=
  mk_bot_eq_mk_bot.mp (mk_rep (mk ⊥ H β))

section Orbit

open scoped Pointwise

variable [IsHeckeTriple Δ H H]

open Classical in
/-- The orbit of a left coset representative `β` under a double coset representative `g`:
the left cosets `βσᵢgH` over the decomposition `HgH = ⊔ᵢ σᵢgH`. -/
noncomputable def smulOrbit (H : Subgroup G) [IsHeckeTriple Δ H H] (g β : Δ) :
    Finset (HeckeCoset Δ ⊥ H) :=
  Finset.univ.image fun i : DecompQuotient H H (g : G) ↦
    mk ⊥ H ⟨(β : G) * i.out * g,
      Δ.mul_mem (Δ.mul_mem β.2 (IsHeckeTriple.mem_of_mem_left H i.out.2)) g.2⟩

lemma smulOrbit_nonempty (g β : Δ) : (smulOrbit H g β).Nonempty := by
  classical
  exact (Finset.univ_nonempty).image _

/-- The conjugation criterion for the stabilizer subgroup indexing `DecompQuotient`. -/
private lemma conj_mem_of_stabilizer (g : G)
    (n : (ConjAct.toConjAct g • H).subgroupOf H) : g⁻¹ * (n : G) * g ∈ H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simpa [ConjAct.ofConjAct_toConjAct] using hn

private lemma smulOrbit_subset {g β₁ β₂ : Δ} {k : G} (hk : k ∈ H)
    (hβ : (β₂ : G) = (β₁ : G) * k) : smulOrbit H g β₁ ⊆ smulOrbit H g β₂ := by
  classical
  intro x hx
  simp only [smulOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨i, hi⟩ := hx
  set j : DecompQuotient H H (g : G) :=
    QuotientGroup.mk ⟨k⁻¹ * i.out, H.mul_mem (H.inv_mem hk) i.out.2⟩ with hj
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g : G) • H).subgroupOf H)
    (⟨k⁻¹ * i.out, H.mul_mem (H.inv_mem hk) i.out.2⟩ : H)
  have hout : ((j.out : H) : G) = k⁻¹ * (i.out : G) * n := by
    rw [hj]
    simpa [Subgroup.coe_mul, mul_assoc] using congrArg (Subtype.val : H → G) hn
  refine ⟨j, ?_⟩
  rw [← hi]
  refine mk_bot_eq_mk_bot.mpr ?_
  -- `mk_eq_mk` lands in the `leftRel`-comap relation of the setoid; its membership statement
  -- coincides with the displayed `H`-membership only through the definitional unfolding of
  -- `QuotientGroup.leftRel` and the `Δ`-subtype coercions, which no rewriting lemma states
  change ((β₂ : G) * ((j.out : H) : G) * (g : G))⁻¹ * ((β₁ : G) * ((i.out : H) : G) * g) ∈ H
  have key : ((β₂ : G) * ((j.out : H) : G) * (g : G))⁻¹ *
      ((β₁ : G) * ((i.out : H) : G) * g) = (g : G)⁻¹ * (n : G)⁻¹ * g := by
    rw [hout, hβ]
    group
  rw [key]
  simpa [mul_assoc] using H.inv_mem (conj_mem_of_stabilizer (g : G) n)

/-- The orbit depends on `β` only through its left coset. -/
lemma smulOrbit_congr (g : Δ) {β₁ β₂ : Δ} (h : mk ⊥ H β₁ = mk ⊥ H β₂) :
    smulOrbit H g β₁ = smulOrbit H g β₂ := by
  have hk := mk_bot_eq_mk_bot.mp h
  refine Finset.Subset.antisymm
    (smulOrbit_subset hk (by group))
    (smulOrbit_subset (H.inv_mem hk) ?_)
  rw [mul_inv_rev, inv_inv]
  group

open scoped Pointwise in
private lemma smulOrbit_map_injective (g β : Δ) :
    Function.Injective fun i : DecompQuotient H H (g : G) ↦
      (mk ⊥ H ⟨(β : G) * i.out * g,
        Δ.mul_mem (Δ.mul_mem β.2 (IsHeckeTriple.mem_of_mem_left H i.out.2)) g.2⟩ :
        HeckeCoset Δ ⊥ H) := by
  intro i₁ i₂ heq
  have hmem : ((β : G) * ((i₁.out : H) : G) * (g : G))⁻¹ *
      ((β : G) * ((i₂.out : H) : G) * (g : G)) ∈ H := mk_bot_eq_mk_bot.mp heq
  have hcoset : ((((i₁.out : H) : G) * (g : G) : G) : G ⧸ H) =
      ((((i₂.out : H) : G) * (g : G) : G) : G ⧸ H) := by
    rw [QuotientGroup.eq]
    have hshape : ((β : G) * ((i₁.out : H) : G) * (g : G))⁻¹ *
        ((β : G) * ((i₂.out : H) : G) * (g : G)) =
        (((i₁.out : H) : G) * g)⁻¹ * (((i₂.out : H) : G) * g) := by group
    exact hshape ▸ hmem
  exact mk_out_mul_injective H H (g : G) hcoset

/-- The orbit of a left coset under `g` has exactly as many elements as the decomposition
`HgH = ⊔ᵢ σᵢgH`: the map `i ↦ βσᵢgH` is injective. -/
lemma smulOrbit_card (g β : Δ) :
    (smulOrbit H g β).card = Fintype.card (DecompQuotient H H (g : G)) := by
  classical
  rw [smulOrbit, Finset.card_image_of_injective _ (smulOrbit_map_injective g β),
    Finset.card_univ]

/-- Orbits of representatives of distinct double cosets on a common left coset are
disjoint. -/
lemma smulOrbit_disjoint {g₁ g₂ : Δ} (β : Δ)
    (hne : HeckeCoset.mk H H g₁ ≠ HeckeCoset.mk H H g₂) :
    Disjoint (smulOrbit H g₁ β) (smulOrbit H g₂ β) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [smulOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hx₁ hx₂
  obtain ⟨i₁, hi₁⟩ := hx₁
  obtain ⟨i₂, hi₂⟩ := hx₂
  have hmem : ((β : G) * ((i₁.out : H) : G) * (g₁ : G))⁻¹ *
      ((β : G) * ((i₂.out : H) : G) * (g₂ : G)) ∈ H :=
    mk_bot_eq_mk_bot.mp (hi₁.trans hi₂.symm)
  refine hne (HeckeCoset.mk_eq_mk_of_mem (mem_doubleCoset.mpr
    ⟨((i₁.out : H) : G)⁻¹ * ((i₂.out : H) : G),
      H.mul_mem (H.inv_mem i₁.out.2) i₂.out.2,
      (((β : G) * ((i₁.out : H) : G) * (g₁ : G))⁻¹ *
        ((β : G) * ((i₂.out : H) : G) * (g₂ : G)))⁻¹,
      H.inv_mem hmem, by group⟩))

end Orbit

end HeckeCoset

namespace HeckeLeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule

variable [IsHeckeTriple Δ H H] {R : Type*} [NonUnitalNonAssocSemiring R]

/-- The action of the Hecke ring on the free module of left cosets: a double coset acts on
a left coset by summing over its orbit, extended biadditively. -/
noncomputable instance instSMulHeckeLeftCosetModule :
    SMul (𝕋 Δ H R) (HeckeCoset Δ ⊥ H →₀ R) where
  smul t m := t.sum fun D b₁ ↦ m.sum fun q b₂ ↦
    ∑ i ∈ smulOrbit H D.rep q.rep, Finsupp.single i (b₁ * b₂)

/-- The defining formula of the action. -/
lemma smul_eq_sum (t : 𝕋 Δ H R) (m : HeckeCoset Δ ⊥ H →₀ R) :
    t • m = t.sum fun D b₁ ↦ m.sum fun q b₂ ↦
      ∑ i ∈ smulOrbit H D.rep q.rep, Finsupp.single i (b₁ * b₂) :=
  (rfl)

/-- The action of a basis element of the Hecke ring on a basis element of the module. -/
lemma single_smul_single (D : HeckeCoset Δ H H) (q : HeckeCoset Δ ⊥ H) (a b : R) :
    HeckeCosetModule.single R D a • (Finsupp.single q b : HeckeCoset Δ ⊥ H →₀ R) =
      ∑ i ∈ smulOrbit H D.rep q.rep, Finsupp.single i (a * b) := by
  classical
  rw [smul_eq_sum,
    HeckeCosetModule.sum_single_index R (by rw [Finsupp.sum_single_index (by simp)]; simp),
    Finsupp.sum_single_index (by simp)]

/-- The action is additive in the Hecke-ring argument. -/
@[simp]
lemma add_smul (t₁ t₂ : 𝕋 Δ H R) (m : HeckeCoset Δ ⊥ H →₀ R) :
    (t₁ + t₂) • m = t₁ • m + t₂ • m := by
  classical
  simp only [smul_eq_sum]
  refine Finsupp.sum_add_index' (fun D ↦ ?_) fun D b₁ b₂ ↦ ?_
  · refine (Finsupp.sum_congr (g2 := fun _ _ ↦ 0) fun q _ ↦ ?_).trans
      (Finsupp.sum_fun_zero m)
    exact Finset.sum_eq_zero fun i _ ↦ by simp
  · refine ((Finsupp.sum_congr fun q _ ↦ ?_).trans Finsupp.sum_add)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [add_mul, Finsupp.single_add]

/-- The action is additive in the module argument. -/
@[simp]
lemma smul_add (t : 𝕋 Δ H R) (m₁ m₂ : HeckeCoset Δ ⊥ H →₀ R) :
    t • (m₁ + m₂) = t • m₁ + t • m₂ := by
  classical
  simp only [smul_eq_sum]
  refine (Finsupp.sum_congr fun D b₁ ↦ ?_).trans Finsupp.sum_add
  refine Finsupp.sum_add_index' (fun q ↦ ?_) fun q b₂ b₃ ↦ ?_
  · exact Finset.sum_eq_zero fun i _ ↦ by simp
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_add, Finsupp.single_add]

/-- The zero element of the Hecke ring acts as zero. -/
@[simp]
lemma zero_smul (m : HeckeCoset Δ ⊥ H →₀ R) : (0 : 𝕋 Δ H R) • m = 0 := by
  rw [smul_eq_sum]
  exact Finsupp.sum_zero_index

/-- Every Hecke-ring element acts as zero on zero. -/
@[simp]
lemma smul_zero (t : 𝕋 Δ H R) : t • (0 : HeckeCoset Δ ⊥ H →₀ R) = 0 := by
  rw [smul_eq_sum]
  simp only [Finsupp.sum_zero_index]
  exact Finsupp.sum_fun_zero t

end HeckeLeftCosetModule

namespace HeckeLeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule

variable [IsHeckeTriple Δ H H] {R : Type*} [NonAssocSemiring R]

/-- Reading off a coefficient of the action on the identity basis element: at any member of
the orbit of `D`, the coefficient of `t • [H]` is the coefficient of `t` at `D`. -/
private lemma smul_single_one_apply (t : 𝕋 Δ H R) (D : HeckeCoset Δ H H)
    {q : HeckeCoset Δ ⊥ H}
    (hq : q ∈ smulOrbit H D.rep (1 : HeckeCoset Δ ⊥ H).rep) :
    (t • (Finsupp.single 1 1 : HeckeCoset Δ ⊥ H →₀ R)) q = t D := by
  classical
  have hinner : ∀ (D' : HeckeCoset Δ H H) (b₁ : R),
      (Finsupp.single (1 : HeckeCoset Δ ⊥ H) (1 : R)).sum (fun q' b₂ ↦
        ∑ i ∈ smulOrbit H D'.rep q'.rep, Finsupp.single i (b₁ * b₂)) =
      ∑ i ∈ smulOrbit H D'.rep (1 : HeckeCoset Δ ⊥ H).rep, Finsupp.single i b₁ := by
    intro D' b₁
    rw [Finsupp.sum_single_index (by simp)]
    simp
  have hsum : (t.sum fun D' b₁ ↦
        (Finsupp.single (1 : HeckeCoset Δ ⊥ H) (1 : R)).sum fun q' b₂ ↦
          ∑ i ∈ smulOrbit H D'.rep q'.rep, Finsupp.single i (b₁ * b₂)) =
      t.sum fun D' b₁ ↦
        ∑ i ∈ smulOrbit H D'.rep (1 : HeckeCoset Δ ⊥ H).rep, Finsupp.single i b₁ :=
    Finsupp.sum_congr fun D' _ ↦ hinner D' (t D')
  rw [smul_eq_sum, hsum]
  simp only [Finsupp.sum, Finsupp.finsetSum_apply]
  have hzero : ∀ D' ∈ t.support, D' ≠ D →
      ∑ i ∈ smulOrbit H D'.rep (1 : HeckeCoset Δ ⊥ H).rep,
        (Finsupp.single i (t D') : HeckeCoset Δ ⊥ H →₀ R) q = 0 := by
    intro D' _ hne
    refine Finset.sum_eq_zero fun i hi ↦ Finsupp.single_apply_eq_zero.mpr fun heq ↦ ?_
    have hne' : HeckeCoset.mk H H D'.rep ≠ HeckeCoset.mk H H D.rep := by
      simpa [HeckeCoset.mk_rep] using hne
    exact absurd hq (Finset.disjoint_left.mp (smulOrbit_disjoint _ hne') (heq ▸ hi))
  have hread : ∀ b : R,
      ∑ i ∈ smulOrbit H D.rep (1 : HeckeCoset Δ ⊥ H).rep,
        (Finsupp.single i b : HeckeCoset Δ ⊥ H →₀ R) q = b := by
    intro b
    rw [Finset.sum_eq_single_of_mem q hq fun i _ hne ↦
      Finsupp.single_apply_eq_zero.mpr fun heq ↦ absurd heq.symm hne]
    simp
  exact (Finset.sum_eq_single D hzero fun hD ↦
    (hread (t D)).trans (Finsupp.notMem_support_iff.mp hD)).trans (hread (t D))

/-- The action of the Hecke ring on the module of left cosets is faithful. -/
lemma eq_of_smul_eq_smul {t₁ t₂ : 𝕋 Δ H R}
    (h : ∀ m : HeckeCoset Δ ⊥ H →₀ R, t₁ • m = t₂ • m) : t₁ = t₂ := by
  classical
  refine Finsupp.ext fun D ↦ ?_
  obtain ⟨q, hq⟩ := smulOrbit_nonempty (H := H) D.rep (1 : HeckeCoset Δ ⊥ H).rep
  have h1 := congrArg (fun m ↦ m q) (h (Finsupp.single 1 1))
  rwa [smul_single_one_apply t₁ D hq, smul_single_one_apply t₂ D hq] at h1

/-- The scalar operations of the Hecke ring on the left-coset module are faithful, as an
instance. -/
noncomputable instance instFaithfulSMul :
    FaithfulSMul (𝕋 Δ H R) (HeckeCoset Δ ⊥ H →₀ R) where
  eq_of_smul_eq_smul := eq_of_smul_eq_smul

end HeckeLeftCosetModule
