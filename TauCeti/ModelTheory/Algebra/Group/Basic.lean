/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.LanguageMap
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.ModelTheory.Complexity
public import Mathlib.Algebra.Group.Ext

/-!
# The first-order language of groups

The language of groups has symbols for multiplication, inverse, and identity. Adding named
constants gives the coefficient language used to translate group terms into free-group words.
A coefficient map supplies the interpretation of those constants in any group.

## Main definitions

`Language.group.theory` consists of the associativity, identity, and inverse sentences.
`Language.group.homomorphism` turns a coefficient-preserving group homomorphism into a
homomorphism of coefficient-language structures.

## Main results

Every group satisfies the group theory under its standard interpretation (`models_theory`).
Conversely, `groupOfModel` equips any model with a group structure whose operations are the
interpreted symbols. Term evaluation commutes with coefficient-preserving homomorphisms
(`realize_homomorphism`).

## References

* O. Kharlampovich and A. Myasnikov, *Implicit function theorem over free groups*, §2.3.
-/

public section

namespace FirstOrder

/-- The three function symbols in the first-order language of groups. -/
inductive groupFunc : ℕ → Type
  | one : groupFunc 0
  | inv : groupFunc 1
  | mul : groupFunc 2
  deriving DecidableEq

namespace Language

/-- The first-order language with multiplication, inverse, identity, and equality. -/
@[expose] def group : Language :=
  { Functions := groupFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace group

/-- The symbol for the identity element. -/
abbrev one : Language.group.Functions 0 := groupFunc.one

/-- The symbol for inversion. -/
abbrev inv : Language.group.Functions 1 := groupFunc.inv

/-- The symbol for multiplication. -/
abbrev mul : Language.group.Functions 2 := groupFunc.mul

/-- The first-order language of groups with constants named by `A`. -/
abbrev Lcoeff (A : Type*) : Language := Language.group[[A]]

/-- Interpret the group symbols using the operations of a group. -/
instance instStructure (G : Type*) [Group G] : Language.group.Structure G where
  funMap := fun f x =>
    match f with
    | .one => 1
    | .inv => (x 0)⁻¹
    | .mul => x 0 * x 1
  RelMap := fun r _ => isEmptyElim r

/-- Interpret the coefficient symbols by a chosen map into a group. -/
@[expose, instance_reducible] def coeffStructure (G A : Type*) [Group G] (c : A → G) :
    (Lcoeff A).Structure G := by
  letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  infer_instance

@[simp] theorem funMap_one (G : Type*) [Group G] (x : Fin 0 → G) :
    Language.Structure.funMap one x = (1 : G) := rfl

@[simp] theorem funMap_inv (G : Type*) [Group G] (x : Fin 1 → G) :
    Language.Structure.funMap inv x = (x 0)⁻¹ := rfl

@[simp] theorem funMap_mul (G : Type*) [Group G] (x : Fin 2 → G) :
    Language.Structure.funMap mul x = x 0 * x 1 := rfl

@[simp] theorem coeffStructure_funMap_one (G A : Type*) [Group G] (c : A → G)
    (x : Fin 0 → G) :
    @Language.Structure.funMap (Lcoeff A) G (coeffStructure G A c) 0
      (Sum.inl one) x = 1 := rfl

@[simp] theorem coeffStructure_funMap_inv (G A : Type*) [Group G] (c : A → G)
    (x : Fin 1 → G) :
    @Language.Structure.funMap (Lcoeff A) G (coeffStructure G A c) 1
      (Sum.inl inv) x = (x 0)⁻¹ := rfl

@[simp] theorem coeffStructure_funMap_mul (G A : Type*) [Group G] (c : A → G)
    (x : Fin 2 → G) :
    @Language.Structure.funMap (Lcoeff A) G (coeffStructure G A c) 2
      (Sum.inl mul) x = x 0 * x 1 := rfl

@[simp] theorem coeffStructure_funMap_coeff (G A : Type*) [Group G] (c : A → G)
    (a : A) (x : Fin 0 → G) :
    @Language.Structure.funMap (Lcoeff A) G (coeffStructure G A c) 0
      (Sum.inr a) x = c a := rfl

/-- Interpret a basis coefficient in the free group on that basis. -/
@[instance_reducible] def freeGroupStructure (A : Type*) :
    (Lcoeff A).Structure (FreeGroup A) :=
  coeffStructure (FreeGroup A) A FreeGroup.of

variable {G A X : Type*} [Group G]

/-- Apply inversion to a group-language term. -/
@[expose] def invTerm (t : Language.group.Term X) : Language.group.Term X :=
  inv.apply₁ t

/-- Multiply two group-language terms. -/
@[expose] def mulTerm (s t : Language.group.Term X) : Language.group.Term X :=
  mul.apply₂ s t

/-- The identity as a group-language term. -/
@[expose] def oneTerm : Language.group.Term X :=
  @Language.Constants.term Language.group X one

@[simp] theorem realize_one (v : X → G) : (oneTerm : Language.group.Term X).realize v = 1 :=
  rfl

@[simp] theorem realize_inv (v : X → G) (t : Language.group.Term X) :
    (invTerm t).realize v = (t.realize v)⁻¹ := by
  simp [invTerm]

@[simp] theorem realize_mul (v : X → G) (s t : Language.group.Term X) :
    (mulTerm s t).realize v = s.realize v * t.realize v := by
  simp [mulTerm]

/-- The named coefficient term in the extended group language. -/
@[expose] def coeffTerm (a : A) : (Lcoeff A).Term X :=
  (Language.group.con a).term

/-- Apply inversion to a term with coefficients. -/
@[expose] def coeffInvTerm (t : (Lcoeff A).Term X) : (Lcoeff A).Term X :=
  Language.Functions.apply₁ (Sum.inl inv : (Lcoeff A).Functions 1) t

/-- Multiply two terms with coefficients. -/
@[expose] def coeffMulTerm (s t : (Lcoeff A).Term X) : (Lcoeff A).Term X :=
  Language.Functions.apply₂ (Sum.inl mul : (Lcoeff A).Functions 2) s t

/-- The identity term in the coefficient language. -/
@[expose] def coeffOneTerm : (Lcoeff A).Term X :=
  @Language.Constants.term (Lcoeff A) X (Sum.inl one)

@[simp] theorem realize_coeff (c : A → G) (v : X → G) (a : A) :
    letI := coeffStructure G A c
    (coeffTerm a).realize v = c a := by
  simp only [coeffTerm, Language.Term.realize_constants]
  exact coeffStructure_funMap_coeff G A c a default

@[simp] theorem realize_coeffInvTerm (c : A → G) (v : X → G)
    (t : (Lcoeff A).Term X) :
    letI := coeffStructure G A c
    (coeffInvTerm t).realize v = (t.realize v)⁻¹ := by
  let _ : (Lcoeff A).Structure G := coeffStructure G A c
  change @Language.Structure.funMap (Lcoeff A) G (coeffStructure G A c) 1
    (Sum.inl inv) ![t.realize v] = (t.realize v)⁻¹
  exact coeffStructure_funMap_inv G A c _

@[simp] theorem realize_coeffMulTerm (c : A → G) (v : X → G)
    (s t : (Lcoeff A).Term X) :
    letI := coeffStructure G A c
    (coeffMulTerm s t).realize v = s.realize v * t.realize v := by
  let _ : (Lcoeff A).Structure G := coeffStructure G A c
  change @Language.Structure.funMap (Lcoeff A) G (coeffStructure G A c) 2
    (Sum.inl mul) ![s.realize v, t.realize v] = s.realize v * t.realize v
  exact coeffStructure_funMap_mul G A c _

@[simp] theorem realize_coeffOneTerm (c : A → G) (v : X → G) :
    letI := coeffStructure G A c
    (coeffOneTerm : (Lcoeff A).Term X).realize v = 1 := by
  change @Language.Structure.funMap (Lcoeff A) G (coeffStructure G A c) 0
    (Sum.inl one) default = 1
  exact coeffStructure_funMap_one G A c default

end group

end Language

end FirstOrder

namespace FirstOrder.Language.group

/-- A coefficient-preserving group homomorphism preserves every symbol of the coefficient
language. -/
@[expose]
def homomorphism {G H A : Type*} [Group G] [Group H]
    (cG : A → G) (cH : A → H) (φ : G →* H) (hc : ∀ a, φ (cG a) = cH a) :
    @FirstOrder.Language.Hom (Lcoeff A) G H
      (coeffStructure G A cG) (coeffStructure H A cH) := by
  letI : (Lcoeff A).Structure G := coeffStructure G A cG
  letI : (Lcoeff A).Structure H := coeffStructure H A cH
  refine ⟨φ, ?_, ?_⟩
  · intro n f x
    -- The sum structure interprets left symbols by the group operations and right symbols by cG/cH.
    cases f with
    | inl f =>
      cases f with
      | one => exact φ.map_one
      | inv => exact φ.map_inv (x 0)
      | mul => exact φ.map_mul (x 0) (x 1)
    | inr f =>
      cases n with
      | zero => exact hc f
      | succ n => exact isEmptyElim f
  · intro n r x h
    cases r with
    | inl r => exact isEmptyElim r
    | inr r => exact isEmptyElim r

@[simp] theorem homomorphism_apply {G H A : Type*} [Group G] [Group H]
    (cG : A → G) (cH : A → H) (φ : G →* H) (hc : ∀ a, φ (cG a) = cH a)
    (x : G) : homomorphism cG cH φ hc x = φ x := rfl

@[simp] theorem coe_homomorphism {G H A : Type*} [Group G] [Group H]
    (cG : A → G) (cH : A → H) (φ : G →* H) (hc : ∀ a, φ (cG a) = cH a) :
    ⇑(homomorphism cG cH φ hc) = φ := rfl

/-- Evaluation of a coefficient term commutes with a coefficient-preserving group homomorphism. -/
theorem realize_homomorphism {G H A X : Type*} [Group G] [Group H]
    (cG : A → G) (cH : A → H) (φ : G →* H)
    (hc : ∀ a, φ (cG a) = cH a) (t : (Lcoeff A).Term X) (v : X → G) :
    @FirstOrder.Language.Term.realize (Lcoeff A) H (coeffStructure H A cH) X
      (φ ∘ v) t =
      φ (@FirstOrder.Language.Term.realize (Lcoeff A) G (coeffStructure G A cG) X v t) := by
  let _ : (Lcoeff A).Structure G := coeffStructure G A cG
  let _ : (Lcoeff A).Structure H := coeffStructure H A cH
  exact FirstOrder.Language.HomClass.realize_term
    (homomorphism cG cH φ hc) (v := v) (t := t)

end FirstOrder.Language.group

namespace FirstOrder.Language.group

open FirstOrder

/-- Universally close a formula whose free variables are indexed by `Fin n`. -/
private def forallVariables {n : ℕ} (φ : Language.group.Formula (Fin n)) :
    Language.group.Sentence :=
  (Language.BoundedFormula.relabel Sum.inr φ).alls

variable {M : Type*} [Language.group.Structure M]

@[simp] private theorem realize_forallVariables {n : ℕ}
    (φ : Language.group.Formula (Fin n)) :
    M ⊨ forallVariables φ ↔ ∀ x : Fin n → M, φ.Realize x := by
  simp only [forallVariables, Language.Sentence.Realize,
    Language.BoundedFormula.realize_alls, Language.Formula.realize_relabel_sumInr, Nat.add_zero]

/-- Associativity as a sentence of the group language. -/
def assocSentence : Language.group.Sentence :=
  forallVariables <|
    (mulTerm (mulTerm (.var (0 : Fin 3)) (.var 1)) (.var 2)).equal
      (mulTerm (.var 0) (mulTerm (.var 1) (.var 2)))

/-- Both identity laws as a sentence of the group language. -/
def identitySentence : Language.group.Sentence :=
  forallVariables <|
    (mulTerm oneTerm (.var (0 : Fin 1))).equal (.var 0) ⊓
      (mulTerm (.var 0) oneTerm).equal (.var 0)

/-- Both inverse laws as a sentence of the group language. -/
def inverseSentence : Language.group.Sentence :=
  forallVariables <|
    (mulTerm (invTerm (.var (0 : Fin 1))) (.var 0)).equal oneTerm ⊓
      (mulTerm (.var 0) (invTerm (.var 0))).equal oneTerm

/-- The first-order theory consisting of the associativity, identity, and inverse axioms. -/
def theory : Language.group.Theory :=
  {assocSentence, identitySentence, inverseSentence}

/-- The coefficient sentence asserting that two named elements commute. -/
def commSentence {A : Type*} (a b : A) : (Lcoeff A).Sentence :=
  (coeffMulTerm (coeffTerm a) (coeffTerm b)).equal
    (coeffMulTerm (coeffTerm b) (coeffTerm a))

@[simp] theorem realize_commSentence {G A : Type*} [Group G] (c : A → G) (a b : A) :
    letI := coeffStructure G A c
    G ⊨ commSentence a b ↔ c a * c b = c b * c a := by
  let _ : (Lcoeff A).Structure G := coeffStructure G A c
  simp only [commSentence, Language.Sentence.Realize, Language.Formula.realize_equal,
    realize_coeffMulTerm, realize_coeff]

/-- Distinct free generators do not satisfy the coefficient commutativity sentence. -/
theorem realize_comm_false :
    letI := freeGroupStructure (Fin 2)
    ¬ (FreeGroup (Fin 2)) ⊨ commSentence (0 : Fin 2) 1 := by
  intro h
  have hc : Commute (FreeGroup.of (0 : Fin 2)) (FreeGroup.of 1) :=
    (realize_commSentence FreeGroup.of 0 1).mp h
  have heq : (0 : Fin 2) = 1 := FreeGroup.eq_of_commute_of_of hc
  contradiction

/-- The standard basis of an abelian group satisfies coefficient commutativity. -/
theorem realize_comm_true :
    let c : Fin 2 → Multiplicative (Fin 2 → ℤ) :=
      fun a => Multiplicative.ofAdd (Pi.single a 1)
    letI := coeffStructure (Multiplicative (Fin 2 → ℤ)) (Fin 2) c
    Multiplicative (Fin 2 → ℤ) ⊨ commSentence (0 : Fin 2) 1 := by
  exact (realize_commSentence _ 0 1).mpr (mul_comm _ _)

/-- Every atomic coefficient-language sentence holds in the trivial group. -/
theorem trivial_models {A : Type*} (c : A → Multiplicative (Fin 0 → ℤ))
    (φ : (Lcoeff A).Sentence)
    (hφ : φ.IsAtomic) :
    letI := coeffStructure (Multiplicative (Fin 0 → ℤ)) A c
    Multiplicative (Fin 0 → ℤ) ⊨ φ := by
  cases hφ with
  | equal _ _ => exact Subsingleton.elim _ _
  | rel r _ =>
    cases r with
    | inl r => exact isEmptyElim r
    | inr r => exact isEmptyElim r

@[simp] theorem realize_assocSentence (M : Type*) [Language.group.Structure M] :
    M ⊨ assocSentence ↔ ∀ x : Fin 3 → M,
      Language.Structure.funMap mul
        ![Language.Structure.funMap mul ![x 0, x 1], x 2] =
        Language.Structure.funMap mul
          ![x 0, Language.Structure.funMap mul ![x 1, x 2] ] := by
  simp [assocSentence, mulTerm]

@[simp] theorem realize_identitySentence (M : Type*) [Language.group.Structure M] :
    M ⊨ identitySentence ↔ ∀ x : Fin 1 → M,
      Language.Structure.funMap mul ![Language.Structure.funMap one default, x 0] = x 0 ∧
        Language.Structure.funMap mul ![x 0, Language.Structure.funMap one default] = x 0 := by
  simp [identitySentence, mulTerm, oneTerm, Language.funMap_eq_coe_constants]

@[simp] theorem realize_inverseSentence (M : Type*) [Language.group.Structure M] :
    M ⊨ inverseSentence ↔ ∀ x : Fin 1 → M,
      Language.Structure.funMap mul
        ![Language.Structure.funMap inv ![x 0], x 0] =
          Language.Structure.funMap one default ∧
        Language.Structure.funMap mul
          ![x 0, Language.Structure.funMap inv ![x 0] ] =
            Language.Structure.funMap one default := by
  simp [inverseSentence, mulTerm, invTerm, oneTerm, Language.funMap_eq_coe_constants]

variable {G : Type*} [Group G]

/-- Every group satisfies the first-order group axioms under the standard interpretation. -/
instance models_theory : G ⊨ theory := by
  constructor
  intro φ hφ
  simp only [theory, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
  rcases hφ with rfl | rfl | rfl
  · simp [assocSentence, mul_assoc]
  · simp [identitySentence]
  · simp [inverseSentence]

/-- The operations interpreted by a model of the group axioms form a group. The resulting
group structure uses exactly the interpretations of the three function symbols. -/
@[instance_reducible] def groupOfModel (M : Type*) [Language.group.Structure M]
    [M ⊨ theory] : Group M := by
  letI modelOne : One M := ⟨Language.Structure.funMap one default⟩
  letI modelMul : Mul M := ⟨fun a b => Language.Structure.funMap mul ![a, b]⟩
  letI modelInv : Inv M := ⟨fun a => Language.Structure.funMap inv ![a]⟩
  have ha : M ⊨ assocSentence :=
    theory.realize_sentence_of_mem (by simp [theory])
  have hi : M ⊨ identitySentence :=
    theory.realize_sentence_of_mem (by simp [theory])
  have hv : M ⊨ inverseSentence :=
    theory.realize_sentence_of_mem (by simp [theory])
  have hma := (realize_assocSentence M).mp ha
  have hmi := (realize_identitySentence M).mp hi
  have hmv := (realize_inverseSentence M).mp hv
  refine Group.ofLeftAxioms ?_ ?_ ?_
  · intro a b c
    change Language.Structure.funMap mul
      ![Language.Structure.funMap mul ![a, b], c] =
        Language.Structure.funMap mul ![a, Language.Structure.funMap mul ![b, c] ]
    exact hma ![a, b, c]
  · intro a
    change Language.Structure.funMap mul
      ![Language.Structure.funMap one default, a] = a
    exact (hmi ![a]).1
  · intro a
    change Language.Structure.funMap mul
      ![Language.Structure.funMap inv ![a], a] =
        Language.Structure.funMap one default
    exact (hmv ![a]).1

/-- The group structure obtained from a model has the interpreted identity. -/
@[simp] theorem groupOfModel_one (M : Type*) [Language.group.Structure M] [M ⊨ theory] :
    letI := groupOfModel M
    (1 : M) = Language.Structure.funMap one default := by
  rfl

/-- The group structure obtained from a model has the interpreted multiplication. -/
@[simp] theorem groupOfModel_mul (M : Type*) [Language.group.Structure M] [M ⊨ theory]
    (a b : M) :
    letI := groupOfModel M
    a * b = Language.Structure.funMap mul ![a, b] := by
  rfl

/-- The group structure obtained from a model has the interpreted inverse. -/
@[simp] theorem groupOfModel_inv (M : Type*) [Language.group.Structure M] [M ⊨ theory]
    (a : M) :
    letI := groupOfModel M
    a⁻¹ = Language.Structure.funMap inv ![a] := by
  rfl

/-- Recover the original group structure from its standard language interpretation. -/
theorem groupOfModel_instStructure (G : Type*) [Group G] :
    @groupOfModel G (instStructure G) (models_theory (G := G)) = (inferInstance : Group G) := by
  apply Group.ext
  funext a b
  rfl

/-- Reinterpreting the group induced by a model recovers every original symbol. -/
theorem instStructure_groupOfModel (M : Type*) [Language.group.Structure M] [M ⊨ theory] :
    @instStructure M (groupOfModel M) = (inferInstance : Language.group.Structure M) := by
  let _ : Group M := groupOfModel M
  apply Language.Structure.ext
  · funext n f x
    cases f with
    | one =>
      change (1 : M) = Language.Structure.funMap one x
      rw [groupOfModel_one M]
      congr 1
      funext i
      exact i.elim0
    | inv =>
      change (x 0)⁻¹ = Language.Structure.funMap inv x
      rw [groupOfModel_inv M]
      congr 1
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
    | mul =>
      change x 0 * x 1 = Language.Structure.funMap mul x
      rw [groupOfModel_mul M]
      congr 1
      funext i
      have hi : (i : ℕ) ≤ 1 := Nat.le_of_lt_succ i.isLt
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with h | h
      · have : i = 0 := Fin.ext h
        subst i
        rfl
      · have : i = 1 := Fin.ext h
        subst i
        rfl
  · funext n r x
    exact isEmptyElim r

end FirstOrder.Language.group
