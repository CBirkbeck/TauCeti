/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Zorn
public import TauCeti.GroupTheory.TrivialIntersection

/-!
# CSA groups

A group is CSA if its maximal abelian subgroups are malnormal. The centralizer of a nonidentity
element in such a group is its unique maximal abelian subgroup containing that element. In
particular, commutation is transitive through a nonidentity element. These properties are useful
for the centralizers and equations of free groups and limit groups.

The definition follows Baumslag, Myasnikov and Remeslennikov, *Algebraic geometry over groups I*,
§§1–2.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- An abelian subgroup maximal among abelian subgroups. -/
def IsMaximalAbelian (H : Subgroup G) : Prop :=
  IsMulCommutative H ∧ ∀ K : Subgroup G, IsMulCommutative K → H ≤ K → K ≤ H

/-- A subgroup is maximal abelian exactly when it is abelian and contains every abelian
subgroup above it. -/
theorem isMaximalAbelian_iff (H : Subgroup G) :
    H.IsMaximalAbelian ↔
      IsMulCommutative H ∧ ∀ K : Subgroup G, IsMulCommutative K → H ≤ K → K ≤ H :=
  Iff.rfl

/-- A maximal abelian subgroup is abelian. -/
theorem IsMaximalAbelian.isMulCommutative {H : Subgroup G} (hH : H.IsMaximalAbelian) :
    IsMulCommutative H := hH.1

/-- An abelian subgroup contained in a maximal abelian subgroup equals it. -/
theorem IsMaximalAbelian.eq_of_le {H K : Subgroup G} (hH : H.IsMaximalAbelian)
    (hK : IsMulCommutative K) (hHK : H ≤ K) : H = K :=
  le_antisymm hHK (hH.2 K hK hHK)

/-- Every abelian subgroup is contained in a maximal abelian subgroup. -/
theorem exists_isMaximalAbelian_of_isMulCommutative (H : Subgroup G)
    (hH : IsMulCommutative H) :
    ∃ M : Subgroup G, H ≤ M ∧ M.IsMaximalAbelian := by
  classical
  let S : Set (Subgroup G) := {K | IsMulCommutative K ∧ H ≤ K}
  have hchain : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ K ∈ c, K ≤ ub := by
    intro c hc hcc
    by_cases hne : c.Nonempty
    · let ub : Subgroup G := sSup c
      have hdir : DirectedOn (· ≤ ·) c := hcc.directedOn
      have hcomm : IsMulCommutative ub := by
        apply IsMulCommutative.of_setLike_mul_comm
        intro x hx y hy
        obtain ⟨K, hK, hxK⟩ := (Subgroup.mem_sSup_of_directedOn hne hdir).mp hx
        obtain ⟨L, hL, hyL⟩ := (Subgroup.mem_sSup_of_directedOn hne hdir).mp hy
        obtain ⟨M, hM, hKM, hLM⟩ := hdir K hK L hL
        have : IsMulCommutative M := (hc hM).1
        exact setLike_mul_comm (hKM hxK) (hLM hyL)
      have hHub : H ≤ ub := (hc hne.some_mem).2.trans (le_sSup hne.some_mem)
      exact ⟨ub, ⟨hcomm, hHub⟩, fun K hK => le_sSup hK⟩
    · have hc0 : c = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      exact ⟨H, ⟨hH, le_rfl⟩, by simp [hc0]⟩
  obtain ⟨M, hMS, hmax⟩ := zorn_le₀ S hchain
  exact ⟨M, hMS.2, hMS.1, fun K hK hMK =>
    (hmax ⟨hK, hMS.2.trans hMK⟩ hMK)⟩

end Subgroup

namespace Group

variable (G : Type*) [Group G]

/-- A group is CSA if each maximal abelian subgroup is malnormal. -/
def IsCSA : Prop := ∀ M : Subgroup G, M.IsMaximalAbelian → TauCeti.IsTISubgroup M

/-- Commutation in a group is transitive when the middle element is nonidentity. -/
def IsCommTransitive : Prop :=
  ∀ x y z : G, y ≠ 1 → Commute x y → Commute y z → Commute x z

/-- The defining malnormality condition for a CSA group. -/
theorem isCSA_iff : IsCSA G ↔
    ∀ M : Subgroup G, M.IsMaximalAbelian → TauCeti.IsTISubgroup M := Iff.rfl

/-- The defining condition for commutation transitivity. -/
theorem isCommTransitive_iff : IsCommTransitive G ↔
    ∀ x y z : G, y ≠ 1 → Commute x y → Commute y z → Commute x z := Iff.rfl

variable {G}

/-- Every abelian group is CSA. -/
theorem isCSA_of_isMulCommutative [IsMulCommutative G] : IsCSA G := by
  dsimp [IsCSA]
  intro M hM
  have htop : M = ⊤ := by
    apply hM.eq_of_le (by infer_instance : IsMulCommutative (⊤ : Subgroup G))
    exact le_top
  rw [htop]
  exact TauCeti.isTISubgroup_iff_inf_conj_smul_eq_bot.mpr (by simp)

/-- A maximal abelian subgroup in a CSA group is the centralizer of each of its nonidentity
elements. Hence it is the unique maximal abelian subgroup containing such an element. -/
theorem IsCSA.eq_centralizer_of_mem (hG : IsCSA G) {M : Subgroup G}
    (hM : M.IsMaximalAbelian) {y : G} (hyM : y ∈ M) (hy : y ≠ 1) :
    M = Subgroup.centralizer {y} := by
  have : IsMulCommutative M := hM.1
  apply le_antisymm
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm hx hyM)
  · exact (hG M hM).centralizer_singleton_le hyM hy

/-- The centralizer of a nonidentity element in a CSA group is maximal abelian. -/
theorem IsCSA.centralizer_isMaximalAbelian (hG : IsCSA G) {y : G} (hy : y ≠ 1) :
    (Subgroup.centralizer {y}).IsMaximalAbelian := by
  let H : Subgroup G := Subgroup.closure {y}
  have hH : IsMulCommutative H := by
    apply Subgroup.isMulCommutative_closure
    simp
  obtain ⟨M, hHM, hM⟩ := H.exists_isMaximalAbelian_of_isMulCommutative hH
  have hyM : y ∈ M := hHM (Subgroup.subset_closure (by simp))
  simpa only [hG.eq_centralizer_of_mem hM hyM hy] using hM

/-- CSA groups have transitive commutation through every nonidentity element. -/
theorem IsCSA.isCommTransitive (hG : IsCSA G) : IsCommTransitive G := by
  intro x y z hy hxy hyz
  have hC := (hG.centralizer_isMaximalAbelian hy).isMulCommutative
  have : IsMulCommutative (Subgroup.centralizer {y} : Subgroup G) := hC
  have hx : x ∈ Subgroup.centralizer {y} :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxy.eq
  have hz : z ∈ Subgroup.centralizer {y} :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyz.eq.symm
  exact setLike_mul_comm hx hz

/-- A nonabelian CSA group has trivial center. -/
theorem IsCSA.center_eq_bot (hG : IsCSA G) (h : ¬ IsMulCommutative G) :
    Subgroup.center G = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro z hz
  by_contra hz1
  apply h
  have htrans := hG.isCommTransitive
  exact ⟨⟨fun a b =>
    (htrans a z b hz1 (Subgroup.mem_center_iff.mp hz a)
      (Subgroup.mem_center_iff.mp hz b).symm).eq⟩⟩

/-- An injective homomorphism into a CSA group has CSA domain. -/
theorem IsCSA.of_injective {H : Type*} [Group H] (hG : IsCSA G)
    (f : H →* G) (hf : Function.Injective f) : IsCSA H := by
  intro M hM
  by_cases hbot : M = ⊥
  · subst M
    apply TauCeti.isTISubgroup_iff_inf_conj_smul_eq_bot.mpr
    simp
  · obtain ⟨⟨y, hyM⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hy : y ≠ 1 := fun e => hy1 (Subtype.ext e)
    have hfy : f y ≠ 1 := fun e => hy (hf (by simpa using e))
    let C : Subgroup G := Subgroup.centralizer {f y}
    have hC : C.IsMaximalAbelian := hG.centralizer_isMaximalAbelian hfy
    have : IsMulCommutative C := hC.1
    have hCM : IsMulCommutative (C.comap f) :=
      C.comap_injective_isMulCommutative hf
    have hMC : M ≤ C.comap f := by
      have : IsMulCommutative M := hM.1
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr <|
        by simpa only [map_mul] using congrArg f (setLike_mul_comm hx hyM)
    have hM_eq : M = C.comap f := hM.eq_of_le hCM hMC
    rw [hM_eq]
    apply TauCeti.isTISubgroup_iff_inf_conj_smul_eq_bot.mpr
    intro g hg
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    obtain ⟨hxC, hxConj⟩ := Subgroup.mem_inf.mp hx
    have hfg : f g ∉ C := hg
    have hfginv : (f g)⁻¹ ∉ C := by simpa using hfg
    have hxConj' : g⁻¹ * x * g ∈ C.comap f := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxConj
      simpa [MulAut.smul_def] using hxConj
    have h1 : f x = 1 := by
      apply (hG C hC).eq_one hfginv hxC
      simpa only [Subgroup.mem_comap, map_mul, map_inv, inv_inv] using hxConj'
    exact hf (by simpa using h1)

/-- A product with a nontrivial abelian factor is not CSA if its other factor is nonabelian.
The nonidentity element in the abelian factor commutes with every element, forcing the other
factor to be abelian if commutation were transitive. -/
theorem not_isCSA_prod_of_nontrivial_isMulCommutative {C : Type*} [Group C]
    [IsMulCommutative C] [Nontrivial C] (hG : ¬ IsMulCommutative G) :
    ¬ IsCSA (G × C) := by
  intro hprod
  obtain ⟨a, b, hab⟩ : ∃ a b : G, ¬ Commute a b := by
    by_contra h
    push Not at h
    exact hG ⟨⟨h⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : C, c ≠ 1 := exists_ne 1
  have hxy : Commute ((a, 1) : G × C) (1, c) :=
    Commute.prod (Commute.one_right a) (Commute.one_left c)
  have hyz : Commute ((1, c) : G × C) (b, 1) :=
    Commute.prod (Commute.one_left b) (Commute.one_right c)
  have hpair : Commute ((a, 1) : G × C) (b, 1) :=
    hprod.isCommTransitive _ _ _ (by simpa using hc) hxy hyz
  exact hab (congrArg Prod.fst hpair.eq)

end Group
