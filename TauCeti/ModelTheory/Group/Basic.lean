/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.LanguageMap
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Algebra.Group.MinimalAxioms

/-!
# The first-order language of groups

The language of groups has symbols for multiplication, inverse, and identity. Adding named
constants gives the coefficient language used to translate group terms into free-group words.
A coefficient map supplies the interpretation of those constants in any group.

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
  simp only [invTerm, Language.Term.realize_functions_apply₁]
  rfl

@[simp] theorem realize_mul (v : X → G) (s t : Language.group.Term X) :
    (mulTerm s t).realize v = s.realize v * t.realize v := by
  simp only [mulTerm, Language.Term.realize_functions_apply₂]
  rfl

/-- The named coefficient term in the extended group language. -/
@[expose] def coeffTerm (a : A) : (Lcoeff A).Term X :=
  (Language.group.con a).term

@[simp] theorem realize_coeff (c : A → G) (v : X → G) (a : A) :
    letI := coeffStructure G A c
    (coeffTerm a).realize v = c a := by
  simp only [coeffTerm, Language.Term.realize_constants]
  rfl

end group

end Language

end FirstOrder

namespace FirstOrder.Language.group

/-- A coefficient-preserving group homomorphism preserves every symbol of the coefficient
language. -/
def homomorphism {G H A : Type*} [Group G] [Group H]
    (cG : A → G) (cH : A → H) (φ : G →* H) (hc : ∀ a, φ (cG a) = cH a) :
    @FirstOrder.Language.Hom (Lcoeff A) G H
      (coeffStructure G A cG) (coeffStructure H A cH) := by
  letI : (Lcoeff A).Structure G := coeffStructure G A cG
  letI : (Lcoeff A).Structure H := coeffStructure H A cH
  refine ⟨φ, ?_, ?_⟩
  · intro n f x
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
def forallVariables {n : ℕ} (φ : Language.group.Formula (Fin n)) :
    Language.group.Sentence :=
  (Language.BoundedFormula.relabel Sum.inr φ).alls

variable {M : Type*} [Language.group.Structure M]

@[simp] theorem realize_forallVariables {n : ℕ}
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

/-- The first-order theory generated by the group axioms. -/
def theory : Language.group.Theory :=
  {assocSentence, identitySentence, inverseSentence}

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
  refine Group.ofLeftAxioms ?_ ?_ ?_
  · intro a b c
    have h := (realize_forallVariables (M := M) _).mp ha ![a, b, c]
    -- The local multiplication is the interpretation of the binary symbol.
    change Language.Structure.funMap mul
      ![Language.Structure.funMap mul ![a, b], c] =
        Language.Structure.funMap mul ![a, Language.Structure.funMap mul ![b, c] ]
    simpa [assocSentence, mulTerm] using h
  · intro a
    have h := (realize_forallVariables (M := M) _).mp hi ![a]
    have h' : Language.Structure.funMap mul
        ![Language.Structure.funMap one default, a] = a ∧
        Language.Structure.funMap mul ![a, Language.Structure.funMap one default] = a := by
      simpa [identitySentence, oneTerm, mulTerm,
        Language.funMap_eq_coe_constants] using h
    -- The local identity and multiplication are the symbol interpretations.
    change Language.Structure.funMap mul
      ![Language.Structure.funMap one default, a] = a
    exact h'.1
  · intro a
    have h := (realize_forallVariables (M := M) _).mp hv ![a]
    have h' : Language.Structure.funMap mul
        ![Language.Structure.funMap inv ![a], a] =
        Language.Structure.funMap one default ∧
        Language.Structure.funMap mul ![a, Language.Structure.funMap inv ![a] ] =
          Language.Structure.funMap one default := by
      simpa [inverseSentence, oneTerm, invTerm, mulTerm,
        Language.funMap_eq_coe_constants] using h
    -- The local inverse, identity, and multiplication are the symbol interpretations.
    change Language.Structure.funMap mul
      ![Language.Structure.funMap inv ![a], a] =
        Language.Structure.funMap one default
    exact h'.1

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

end FirstOrder.Language.group
