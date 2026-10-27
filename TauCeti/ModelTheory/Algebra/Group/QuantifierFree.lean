/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Algebra.Group.TermWord
public import TauCeti.GroupTheory.FreeGroup.EqIneqSystem
public import Mathlib.ModelTheory.Complexity

/-!
# Quantifier-free group formulas as finite families of word systems

Every quantifier-free formula in the group language with named coefficients is equivalent,
in every group and for every interpretation of the coefficients, to a finite disjunction of
systems of word equations and inequations. The finite family is independent of the group.
Keeping bound-variable slots in the statement makes the result available for reducing the
matrix of an existential or universal formula.

The equations-and-inequations normal form follows Kharlampovich and Myasnikov,
*Implicit function theorem over free groups*, §2.3.
-/

public section

namespace TauCeti

namespace EqIneqSystem

variable {X A G : Type*} [Group G]

/-- Distribute conjunction over two finite disjunctions of word systems. -/
def disjunctionProduct (S T : List (EqIneqSystem X A)) : List (EqIneqSystem X A) :=
  (S.product T).map fun st => st.1.append st.2

/-- A system occurs in the distributed product exactly when it appends a system from each
input family. -/
@[simp] theorem mem_disjunctionProduct_iff (S T : List (EqIneqSystem X A))
    (U : EqIneqSystem X A) :
    U ∈ disjunctionProduct S T ↔ ∃ s ∈ S, ∃ t ∈ T, s.append t = U := by
  simp only [disjunctionProduct, List.mem_map]
  constructor
  · rintro ⟨⟨s, t⟩, hst, heq⟩
    obtain ⟨hs, ht⟩ := List.mem_product.mp hst
    exact ⟨s, hs, t, ht, heq⟩
  · rintro ⟨s, hs, t, ht, heq⟩
    exact ⟨(s, t), List.mem_product.mpr ⟨hs, ht⟩, heq⟩

/-- Solving a system in a distributed conjunction is equivalent to solving one system
from each input family. -/
theorem exists_isSolution_disjunctionProduct (S T : List (EqIneqSystem X A))
    (v : X → G) (c : A → G) :
    (∃ U ∈ disjunctionProduct S T, U.IsSolution v c) ↔
      (∃ s ∈ S, s.IsSolution v c) ∧ (∃ t ∈ T, t.IsSolution v c) := by
  simp only [mem_disjunctionProduct_iff]
  constructor
  · rintro ⟨U, ⟨s, hs, t, ht, rfl⟩, hU⟩
    exact ⟨⟨s, hs, (isSolution_append s t v c).mp hU |>.1⟩,
      ⟨t, ht, (isSolution_append s t v c).mp hU |>.2⟩⟩
  · rintro ⟨⟨s, hs, hS⟩, ⟨t, ht, hT⟩⟩
    exact ⟨s.append t, ⟨s, hs, t, ht, rfl⟩,
      (isSolution_append s t v c).mpr ⟨hS, hT⟩⟩

end EqIneqSystem

end TauCeti

namespace FirstOrder.Language.group

open FirstOrder TauCeti

variable {X A : Type*} {n : ℕ}

private theorem exists_normalForms
    {φ : Language.group[[A]].BoundedFormula X n} (hφ : φ.IsQF) :
    ∃ (positive negative : List (EqIneqSystem (X ⊕ Fin n) A)),
      ∀ (G : Type*) [Group G] (v : X → G) (c : A → G) (xs : Fin n → G),
        letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
        letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
        (φ.Realize v xs ↔ ∃ S ∈ positive, S.IsSolution (Sum.elim v xs) c) ∧
        (¬φ.Realize v xs ↔ ∃ S ∈ negative, S.IsSolution (Sum.elim v xs) c) := by
  induction hφ with
  | falsum =>
    refine ⟨[], [EqIneqSystem.empty _ _], ?_⟩
    intro G _ v c xs
    simp [BoundedFormula.Realize]
  | of_isAtomic h =>
    cases h with
    | equal t s =>
      let w := Term.toWord t * (Term.toWord s)⁻¹
      refine ⟨[⟨[w], []⟩], [⟨[], [w]⟩], ?_⟩
      intro G _ v c xs
      let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
      let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
      have heq := Term.realize_equal_iff c (Sum.elim v xs) t s
      constructor
      · simpa [EqIneqSystem.isSolution_iff, EqIneqSystem.eval_eq_lift, w] using heq
      · simpa [EqIneqSystem.isSolution_iff, EqIneqSystem.eval_eq_lift, w] using not_congr heq
    | rel R _ =>
      -- The coefficient extension has two empty relation-symbol summands.
      change Empty ⊕ Empty at R
      cases R with
      | inl r => exact isEmptyElim r
      | inr r => exact isEmptyElim r
  | imp h₁ h₂ ih₁ ih₂ =>
    obtain ⟨P₁, N₁, h₁⟩ := ih₁
    obtain ⟨P₂, N₂, h₂⟩ := ih₂
    refine ⟨N₁ ++ P₂, EqIneqSystem.disjunctionProduct P₁ N₂, ?_⟩
    intro G _ v c xs
    let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    obtain ⟨hp₁, hn₁⟩ := h₁ G v c xs
    obtain ⟨hp₂, hn₂⟩ := h₂ G v c xs
    constructor
    · simp only [BoundedFormula.realize_imp, List.mem_append, or_and_right, exists_or]
      rw [← hn₁, ← hp₂]
      tauto
    · rw [BoundedFormula.realize_imp,
        EqIneqSystem.exists_isSolution_disjunctionProduct]
      rw [← hp₁, ← hn₂]
      tauto

/-- A quantifier-free group formula is uniformly a finite disjunction of finite systems of
word equations and inequations. The same family works for every group and coefficient map. -/
theorem quantifierFree_iff_systems
    {φ : Language.group[[A]].BoundedFormula X n} (hφ : φ.IsQF) :
    ∃ systems : List (EqIneqSystem (X ⊕ Fin n) A),
      ∀ (G : Type*) [Group G] (v : X → G) (c : A → G) (xs : Fin n → G),
        letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
        letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
        φ.Realize v xs ↔
          ∃ S ∈ systems, S.IsSolution (Sum.elim v xs) c := by
  obtain ⟨systems, _, h⟩ := exists_normalForms hφ
  exact ⟨systems, fun G _ v c xs => (h G v c xs).1⟩

end FirstOrder.Language.group
