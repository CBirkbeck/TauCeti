/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Tactic.FinCases

/-!
# The first-order language of groups

The language has a constant for the identity, a unary inverse symbol and a binary
multiplication symbol. Adding named coefficients uses Mathlib's `Language.withConstants`.
The interpretation in a group, and the three left-hand group axioms, give the semantic
interface needed to turn group formulas into equations in words.

The choice of symbols and coefficient letters follows Kharlampovich and Myasnikov,
*Implicit function theorem over free groups*, §2.3. The language and structure interface
follows Mathlib's first-order language of rings.
-/

public section

namespace FirstOrder

/-- Function symbols for the identity, inverse and multiplication of a group. -/
inductive groupFunc : ℕ → Type
  | one : groupFunc 0
  | inv : groupFunc 1
  | mul : groupFunc 2
  deriving DecidableEq

/-- The first-order language of groups, with equality as the only atomic relation. -/
@[expose] def Language.group : Language where
  Functions := groupFunc
  Relations := fun _ => Empty

/-- The three left-hand axioms characterizing a group: associativity, identity and inverse. -/
inductive GroupAxiom
  | mulAssoc
  | oneMul
  | invMulCancel

namespace Group

open Language groupFunc Language.Structure

/-- The identity symbol, viewed as a symbol of `Language.group`. -/
abbrev oneFunc : Language.group.Functions 0 := groupFunc.one

/-- The inverse symbol, viewed as a symbol of `Language.group`. -/
abbrev invFunc : Language.group.Functions 1 := groupFunc.inv

/-- The multiplication symbol, viewed as a symbol of `Language.group`. -/
abbrev mulFunc : Language.group.Functions 2 := groupFunc.mul

instance (α : Type*) : One (Language.group.Term α) :=
  ⟨Language.Constants.term oneFunc⟩

instance (α : Type*) : Inv (Language.group.Term α) :=
  ⟨invFunc.apply₁⟩

instance (α : Type*) : Mul (Language.group.Term α) :=
  ⟨mulFunc.apply₂⟩

theorem one_def (α : Type*) :
    (1 : Language.group.Term α) = Language.Constants.term oneFunc := rfl

theorem inv_def (α : Type*) (t : Language.group.Term α) :
    t⁻¹ = invFunc.apply₁ t := rfl

theorem mul_def (α : Type*) (t s : Language.group.Term α) :
    t * s = mulFunc.apply₂ t s := rfl

/-- Interpret the group language using the operations of a group. -/
@[instance_reducible] def structureOfGroup (G : Type*) [Group G] : Language.group.Structure G where
  funMap {n} f := by
    cases f with
    | one => exact fun _ => 1
    | inv => exact fun xs => (xs 0)⁻¹
    | mul => exact fun xs => xs 0 * xs 1
  RelMap r := nomatch r

attribute [instance] structureOfGroup

section GroupStructure

variable {G : Type*} [Group G]

/-- The identity symbol denotes the group identity. -/
@[simp] theorem funMap_one (xs : Fin 0 → G) :
    Language.Structure.funMap oneFunc xs = (1 : G) := (rfl)

/-- The inverse symbol denotes group inversion. -/
@[simp] theorem funMap_inv (xs : Fin 1 → G) :
    Language.Structure.funMap invFunc xs = (xs 0)⁻¹ := (rfl)

/-- The multiplication symbol denotes group multiplication. -/
@[simp] theorem funMap_mul (xs : Fin 2 → G) :
    Language.Structure.funMap mulFunc xs = xs 0 * xs 1 := (rfl)

@[simp] theorem realize_one {α : Type*} (v : α → G) :
    Language.Term.realize v (1 : Language.group.Term α) = 1 := (rfl)

@[simp] theorem realize_inv {α : Type*} (v : α → G) (t : Language.group.Term α) :
    Language.Term.realize v t⁻¹ = (Language.Term.realize v t)⁻¹ := (rfl)

@[simp] theorem realize_mul {α : Type*} (v : α → G) (t s : Language.group.Term α) :
    Language.Term.realize v (t * s) =
      Language.Term.realize v t * Language.Term.realize v s := (rfl)

end GroupStructure

/-- The group language with additional constants named by `A`. -/
abbrev Lcoeff (A : Type*) : Language := Language.group.withConstants A

/-- Interpret the coefficient constants using a map into the group. -/
@[instance_reducible] def coeffStructure (G A : Type*) [Group G] (c : A → G) :
    (Lcoeff A).Structure G :=
  letI := structureOfGroup G
  letI := Language.constantsOn.structure c
  inferInstance

/-- The constant named by `a` denotes the chosen coefficient `c a`. -/
theorem coeffStructure_funMap_con {G A : Type*} [Group G] (c : A → G)
    (a : A) (xs : Fin 0 → G) :
    @Language.Structure.funMap (Lcoeff A) G (coeffStructure G A c) 0 (Sum.inr a) xs =
      c a := by
  rw [Subsingleton.elim xs (![] : Fin 0 → G)]
  rfl

/-- A coefficient term evaluates to its named group element. -/
@[simp] theorem realize_con {G A X : Type*} [Group G] (c : A → G)
    (v : X → G) (a : A) :
    @Language.Term.realize (Lcoeff A) G (coeffStructure G A c) X v
      (Language.Constants.term (Sum.inr a)) = c a := by
  exact coeffStructure_funMap_con c a default

end Group

open Language BoundedFormula

namespace GroupAxiom

/-- The sentence expressing one of the three left-hand group axioms. -/
def toSentence : GroupAxiom → Language.group.Sentence
  | .mulAssoc => ∀' ∀' ∀' (((&0 * &1) * &2) =' (&0 * (&1 * &2)))
  | .oneMul => ∀' (((1 : Language.group.Term _) * &0) =' &0)
  | .invMulCancel => ∀' (((&0 : Language.group.Term _)⁻¹ * &0) =' 1)

/-- The ordinary group law expressed by each first-order group axiom. -/
def toProp (G : Type*) [Mul G] [Inv G] [One G] : GroupAxiom → Prop
  | .mulAssoc => ∀ x y z : G, (x * y) * z = x * (y * z)
  | .oneMul => ∀ x : G, 1 * x = x
  | .invMulCancel => ∀ x : G, x⁻¹ * x = 1

end GroupAxiom

/-- The first-order theory axiomatizing groups. -/
def Language.groupTheory : Language.group.Theory :=
  Set.range GroupAxiom.toSentence

namespace Group

open Language.Structure

section Axioms

/-- The multiplication extracted from a group-language structure. -/
@[instance_reducible] def mulOfStructure (G : Type*) [Language.group.Structure G] : Mul G :=
  ⟨fun x y => funMap mulFunc ![x, y]⟩

/-- The inversion extracted from a group-language structure. -/
@[instance_reducible] def invOfStructure (G : Type*) [Language.group.Structure G] : Inv G :=
  ⟨fun x => funMap invFunc ![x]⟩

/-- The identity extracted from a group-language structure. -/
@[instance_reducible] def oneOfStructure (G : Type*) [Language.group.Structure G] : One G :=
  ⟨funMap oneFunc ![]⟩

variable (G : Type*) [Group G]

/-- A group axiom holds in the canonical interpretation exactly when its group law holds. -/
theorem GroupAxiom.realize_iff_toProp (a : GroupAxiom) :
    (G ⊨ a.toSentence) ↔ a.toProp G := by
  cases a <;> simp [GroupAxiom.toSentence, GroupAxiom.toProp,
    Sentence.Realize, Formula.Realize, Fin.snoc]

/-- Every group with its canonical language structure satisfies the group theory. -/
theorem models_theory : G ⊨ Language.groupTheory := by
  rw [Language.Theory.model_iff]
  intro φ hφ
  obtain ⟨a, rfl⟩ := hφ
  rw [GroupAxiom.realize_iff_toProp]
  cases a <;> simp [GroupAxiom.toProp, mul_assoc, one_mul, inv_mul_cancel]

end Axioms

section Models

variable (G : Type*) [Language.group.Structure G] [G ⊨ Language.groupTheory]

attribute [local instance] mulOfStructure invOfStructure oneOfStructure

/-- Each axiom of a group-language model holds for its extracted operations. -/
theorem GroupAxiom.toProp_of_model (a : GroupAxiom) :
    @GroupAxiom.toProp G (mulOfStructure G) (invOfStructure G) (oneOfStructure G) a := by
  have h : G ⊨ a.toSentence :=
    Language.Theory.realize_sentence_of_mem Language.groupTheory (Set.mem_range_self a)
  -- The changes unfold the operations extracted from the symbols. Arity vectors are then
  -- compared by extensionality in the structure equality below.
  cases a
  · intro x y z
    -- The extracted multiplication and the language symbol are definitionally the same.
    change funMap mulFunc ![funMap mulFunc ![x, y], z] =
      funMap mulFunc ![x, funMap mulFunc ![y, z] ]
    simpa [GroupAxiom.toSentence, Sentence.Realize, Formula.Realize, Fin.snoc,
      mul_def] using h x y z
  · intro x
    change funMap mulFunc ![funMap oneFunc ![], x] = x
    simpa [GroupAxiom.toSentence, Sentence.Realize, Formula.Realize, Fin.snoc,
      one_def, mul_def, Language.constantMap,
      show (![] : Fin 0 → G) = default from Subsingleton.elim _ _]
      using h x
  · intro x
    change funMap mulFunc ![funMap invFunc ![x], x] = funMap oneFunc ![]
    simpa [GroupAxiom.toSentence, Sentence.Realize, Formula.Realize, Fin.snoc,
      one_def, inv_def, mul_def, Language.constantMap,
      show (![] : Fin 0 → G) = default from Subsingleton.elim _ _]
      using h x

/-- A model of the three group axioms carries the group structure given by its symbols. -/
@[instance_reducible] def groupOfModel : _root_.Group G :=
  _root_.Group.ofLeftAxioms
    (GroupAxiom.toProp_of_model G .mulAssoc)
    (GroupAxiom.toProp_of_model G .oneMul)
    (GroupAxiom.toProp_of_model G .invMulCancel)

/-- Reinterpreting the extracted group operations recovers the original language structure. -/
theorem structureOfGroup_groupOfModel :
    letI : _root_.Group G := groupOfModel G
    structureOfGroup G = ‹Language.group.Structure G› := by
  apply Language.Structure.ext
  · funext n f xs
    cases f
    · change funMap oneFunc ![] = funMap oneFunc xs
      congr 1
      exact Subsingleton.elim _ _
    · change funMap invFunc ![xs 0] = funMap invFunc xs
      congr 1
      funext i
      fin_cases i
      rfl
    · change funMap mulFunc ![xs 0, xs 1] = funMap mulFunc xs
      congr 1
      funext i
      fin_cases i <;> rfl
  · funext n r xs
    cases r

end Models

section Homomorphisms

variable {G H A : Type*} [Group G] [Group H]

/-- A group homomorphism is a homomorphism of canonical group-language structures. -/
def homOfMonoidHom (φ : G →* H) :
    Language.group.Hom G H where
  toFun := φ
  map_fun' := by
    intro n f xs
    cases f <;> simp [Language.Structure.funMap]
  map_rel' := by
    intro n r
    cases r

/-- A coefficient-preserving group homomorphism respects the language with named constants. -/
def coeffHomOfMonoidHom (φ : G →* H) (c : A → G) (d : A → H)
    (hc : ∀ a, φ (c a) = d a) :
    @Language.Hom (Lcoeff A) G H (coeffStructure G A c) (coeffStructure H A d) := by
  letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure d
  letI : (Lcoeff A).Structure G := coeffStructure G A c
  letI : (Lcoeff A).Structure H := coeffStructure H A d
  refine { toFun := φ, map_fun' := ?_, map_rel' := ?_ }
  · intro n f xs
    cases f with
    | inl f =>
      rw [Language.withConstants_funMap_sumInl, Language.withConstants_funMap_sumInl]
      convert (homOfMonoidHom φ).map_fun f xs using 1 <;> rfl
    | inr f =>
      cases n with
      | zero =>
        dsimp only [Language.constantsOn, Language.constantsOnFunc] at f
        -- Make the coefficient structure explicit so its characteristic lemma applies.
        change φ (@Language.Structure.funMap (Language.group.withConstants A) G
          (coeffStructure G A c) 0 (Sum.inr f) xs) =
          @Language.Structure.funMap (Language.group.withConstants A) H
            (coeffStructure H A d) 0 (Sum.inr f) (φ ∘ xs)
        simpa only [coeffStructure_funMap_con] using hc f
      | succ n => exact isEmptyElim f
  · intro n r
    cases r with
    | inl r => cases r
    | inr r => cases r

end Homomorphisms

end Group
end FirstOrder
