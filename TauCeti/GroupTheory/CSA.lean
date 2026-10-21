/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TrivialIntersection
public import TauCeti.Algebra.Group.Subgroup.MaximalAbelian
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# CSA groups and commutation transitivity

A CSA group has malnormal maximal abelian subgroups. The maximal abelian subgroup
containing a nonidentity element is its centralizer; this gives commutation
transitivity and makes the definition useful without choosing maximal subgroups.

The malnormality predicate is `TauCeti.IsTISubgroup`.

The CSA formulation and its centralizer consequences follow Baumslag,
Myasnikov and Remeslennikov, *Algebraic geometry over groups I*, §2.1.
-/

public section

namespace Group

variable {G : Type*} [Group G]

/-- A group is CSA if each of its maximal abelian subgroups is malnormal. -/
def IsCSA (G : Type*) [Group G] : Prop :=
  ∀ M : Subgroup G, Maximal (fun H : Subgroup G => IsMulCommutative H) M →
    TauCeti.IsTISubgroup M

/-- A group is CSA exactly when every maximal abelian subgroup is malnormal. -/
theorem isCSA_def : IsCSA G ↔
    ∀ M : Subgroup G, Maximal (fun H : Subgroup G => IsMulCommutative H) M →
      TauCeti.IsTISubgroup M := Iff.rfl

/-- Commutation is transitive through a nonidentity middle element. -/
def IsCommTransitive (G : Type*) [Group G] : Prop :=
  ∀ ⦃x y z : G⦄, y ≠ 1 → Commute x y → Commute y z → Commute x z

/-- The defining condition for commutation transitivity. -/
theorem isCommTransitive_def : IsCommTransitive G ↔
    ∀ ⦃x y z : G⦄, y ≠ 1 → Commute x y → Commute y z → Commute x z := Iff.rfl

namespace IsCommTransitive

/-- Apply commutation transitivity through a nonidentity element. -/
theorem commute (h : IsCommTransitive G) {x y z : G} (hy : y ≠ 1)
    (hxy : Commute x y) (hyz : Commute y z) : Commute x z :=
  isCommTransitive_def.mp h hy hxy hyz

/-- A noncommutative group with transitive commutation has trivial center. -/
theorem center_eq_bot (h : IsCommTransitive G) (hnoncomm : ¬ IsMulCommutative G) :
    Subgroup.center G = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  by_contra hzne
  apply hnoncomm
  rw [← Subgroup.center_eq_top_iff]
  rw [Subgroup.eq_top_iff']
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  have hzx := Subgroup.mem_center_iff.mp hz x
  have hzy := Subgroup.mem_center_iff.mp hz y
  exact h.commute hzne hzy hzx.symm

end IsCommTransitive

/-- Commutation transitivity says exactly that each nontrivial element has an
abelian centralizer. -/
theorem isCommTransitive_iff_centralizer_isMulCommutative :
    IsCommTransitive G ↔
      ∀ x : G, x ≠ 1 → IsMulCommutative (Subgroup.centralizer {x}) := by
  constructor
  · intro h x hx
    apply IsMulCommutative.of_setLike_mul_comm
    intro a ha b hb
    exact h hx (Subgroup.mem_centralizer_singleton_iff.mp ha)
      (Subgroup.mem_centralizer_singleton_iff.mp hb).symm
  · intro h x y z hy hxy hyz
    have hx : x ∈ Subgroup.centralizer {y} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxy
    have hz : z ∈ Subgroup.centralizer {y} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hyz.symm
    exact (isMulCommutative_iff_of_setLike.mp (h y hy)) x hx z hz

namespace IsCSA

/-- A maximal abelian subgroup containing a nonidentity element is its centralizer. -/
theorem eq_centralizer (hG : IsCSA G) {M : Subgroup G}
    (hM : Maximal (fun H : Subgroup G => IsMulCommutative H) M)
    {x : G} (hx : x ∈ M) (hx1 : x ≠ 1) :
    M = Subgroup.centralizer {x} := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hM.1) hg x hx).symm
  · exact (hG M hM).centralizer_singleton_le hx hx1

/-- In a CSA group, the centralizer of a nonidentity element is abelian. -/
theorem centralizer_isMulCommutative (hG : IsCSA G) {x : G} (hx : x ≠ 1) :
    IsMulCommutative (Subgroup.centralizer {x}) := by
  obtain ⟨M, hle, hM⟩ := Subgroup.exists_le_maximalAbelian (Subgroup.zpowers x)
  rw [← hG.eq_centralizer hM (hle (Subgroup.mem_zpowers x)) hx]
  exact hM.1

/-- The centralizer of a nonidentity element is the unique maximal abelian
subgroup that contains it. -/
theorem centralizer_isMaximalAbelian (hG : IsCSA G) {x : G} (hx : x ≠ 1) :
    Maximal (fun H : Subgroup G => IsMulCommutative H)
      (Subgroup.centralizer {x}) := by
  obtain ⟨M, hle, hM⟩ := Subgroup.exists_le_maximalAbelian (Subgroup.zpowers x)
  rw [← hG.eq_centralizer hM (hle (Subgroup.mem_zpowers x)) hx]
  exact hM

/-- The centralizer of a nonidentity element in a CSA group is malnormal. -/
theorem centralizer_isTISubgroup (hG : IsCSA G) {x : G} (hx : x ≠ 1) :
    TauCeti.IsTISubgroup (Subgroup.centralizer {x}) :=
  hG _ (hG.centralizer_isMaximalAbelian hx)

/-- A CSA group has transitive commutation among nonidentity elements. -/
theorem isCommTransitive (hG : IsCSA G) : IsCommTransitive G :=
  isCommTransitive_iff_centralizer_isMulCommutative.mpr
    (fun _ hx => hG.centralizer_isMulCommutative hx)

/-- A noncommutative CSA group has trivial center. -/
theorem center_eq_bot (hG : IsCSA G) (hnoncomm : ¬ IsMulCommutative G) :
    Subgroup.center G = ⊥ :=
  hG.isCommTransitive.center_eq_bot hnoncomm

/-- An injective homomorphism into a CSA group makes its source CSA. -/
theorem of_injective {H : Type*} [Group H] (hG : IsCSA G)
    (f : H →* G) (hf : Function.Injective f) : IsCSA H := by
  intro K hK
  have hmap : IsMulCommutative (K.map f) :=
    @Subgroup.map_isMulCommutative H G _ _ K f hK.1
  obtain ⟨M, hle, hM⟩ := @Subgroup.exists_le_maximalAbelian G _ (K.map f) hmap
  have hcomap : IsMulCommutative (M.comap f) :=
    @Subgroup.comap_injective_isMulCommutative G H _ _ M f hf hM.1
  have hKle : K ≤ M.comap f := by
    intro x hx
    exact hle (Subgroup.mem_map_of_mem f hx)
  have hK_eq : K = M.comap f := hK.eq_of_le hcomap hKle
  apply TauCeti.isTISubgroup_iff_inf_conj_smul_eq_bot.mpr
  intro g hg
  have hfg : f g ∉ M := by
    intro h
    apply hg
    rw [hK_eq]
    exact h
  have hbot := TauCeti.isTISubgroup_iff_inf_conj_smul_eq_bot.mp (hG M hM) (f g) hfg
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  have hxK : x ∈ K := (Subgroup.mem_inf.mp hx).1
  have hxconj := (Subgroup.mem_inf.mp hx).2
  have hfx : f x ∈ M := by
    rw [hK_eq] at hxK
    exact hxK
  have hconjK : g⁻¹ * x * g ∈ K := by
    have h := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp hxconj
    simpa [MulAut.smul_def] using h
  have hfconj : (f g)⁻¹ * f x * f g ∈ M := by
    rw [hK_eq] at hconjK
    simpa [map_mul] using hconjK
  apply hf
  rw [map_one]
  apply (Subgroup.eq_bot_iff_forall _).mp hbot
  apply Subgroup.mem_inf.mpr
  refine ⟨hfx, ?_⟩
  apply (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mpr
  simpa [MulAut.smul_def] using hfconj

/-- Every commutative group is CSA. -/
theorem of_commGroup [IsMulCommutative G] : IsCSA G := by
  intro M hM
  have htop : IsMulCommutative (⊤ : Subgroup G) := inferInstance
  have hMtop : M = ⊤ := hM.eq_of_le htop le_top
  subst M
  apply TauCeti.isTISubgroup_iff_inf_conj_smul_eq_bot.mpr
  intro g hg
  exact (hg (Subgroup.mem_top g)).elim

end IsCSA

/-- A product of a noncommutative group with a nontrivial group
is not commutation transitive: a nonidentity element in the second factor
joins noncommuting elements. -/
theorem not_isCommTransitive_prod_of_not_isMulCommutative {A : Type*}
    [Group A] [Nontrivial A] (hG : ¬ IsMulCommutative G) :
    ¬ IsCommTransitive (G × A) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : G, a * b ≠ b * a := by
    simpa only [isMulCommutative_iff, not_forall] using hG
  obtain ⟨t, ht⟩ := exists_ne (1 : A)
  intro h
  have hmiddle : (1, t) ≠ (1 : G × A) := by simpa using ht
  have hleft : Commute (a, (1 : A)) ((1 : G), t) := by
    simp [commute_iff_eq]
  have hright : Commute ((1 : G), t) (b, (1 : A)) := by
    simp [commute_iff_eq]
  have hfinal := h.commute hmiddle hleft hright
  exact hab (congrArg Prod.fst hfinal)

/-- A product of a noncommutative group with a nontrivial group is not CSA. -/
theorem not_isCSA_prod_of_not_isMulCommutative {A : Type*}
    [Group A] [Nontrivial A] (hG : ¬ IsMulCommutative G) :
    ¬ IsCSA (G × A) := by
  intro h
  exact not_isCommTransitive_prod_of_not_isMulCommutative hG h.isCommTransitive

end Group
