/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Finite systems of equations and inequations over a free group

An equation or inequation with variables `X` and coefficient letters `A` is a word in
`FreeGroup (X ⊕ A)`. A solution assigns group elements to the variables and coefficients,
then evaluates each word by `FreeGroup.lift`. Keeping the two finite lists separate makes
their conjunction available to normal forms for quantifier-free group formulas.

The equation–inequation viewpoint follows Kharlampovich and Myasnikov, *Implicit function
theorem over free groups*, §2.3.
-/

public section

namespace TauCeti.FreeGroup

/-- A finite conjunction of equations and inequations in variables `X` with coefficient
letters `A`. The lists need not be deduplicated: they are finite syntax, and their order has
no effect on solutions. -/
@[ext] structure EqIneqSystem (X A : Type*) where
  /-- Words required to evaluate to the identity. -/
  eqs : List (FreeGroup (X ⊕ A))
  /-- Words required to evaluate away from the identity. -/
  ineqs : List (FreeGroup (X ⊕ A))

namespace EqIneqSystem

variable {X A : Type*} {G H : Type*} [Group G] [Group H]

/-- Evaluation of a word under a variable assignment and a coefficient map. -/
def eval (v : X → G) (c : A → G) : FreeGroup (X ⊕ A) →* G :=
  FreeGroup.lift (Sum.elim v c)

/-- Evaluation is the lift of the assignments on variable and coefficient letters. -/
theorem eval_eq_lift (v : X → G) (c : A → G) :
    eval v c = FreeGroup.lift (Sum.elim v c) := by rfl

/-- Evaluation of a generator selects its variable or coefficient value. -/
@[simp] theorem eval_of (v : X → G) (c : A → G) (i : X ⊕ A) :
    eval v c (FreeGroup.of i) = Sum.elim v c i := by
  simp [eval]

@[simp] theorem eval_of_inl (v : X → G) (c : A → G) (x : X) :
    eval v c (FreeGroup.of (Sum.inl x)) = v x := by
  simp [eval]

@[simp] theorem eval_of_inr (v : X → G) (c : A → G) (a : A) :
    eval v c (FreeGroup.of (Sum.inr a)) = c a := by
  simp [eval]

/-- A variable assignment solves a system when all equations vanish and all inequations
remain nontrivial after evaluation. -/
def IsSolution (S : EqIneqSystem X A) (v : X → G) (c : A → G) : Prop :=
  (∀ w ∈ S.eqs, eval v c w = 1) ∧ (∀ w ∈ S.ineqs, eval v c w ≠ 1)

/-- The empty system places no conditions on an assignment. -/
def empty (X A : Type*) : EqIneqSystem X A := ⟨[], []⟩

/-- The empty system has no equations. -/
@[simp] theorem eqs_empty (X A : Type*) : (empty X A).eqs = [] := by rfl

/-- The empty system has no inequations. -/
@[simp] theorem ineqs_empty (X A : Type*) : (empty X A).ineqs = [] := by rfl

@[simp] theorem isSolution_empty (v : X → G) (c : A → G) :
    (empty X A).IsSolution v c := by
  simp [empty, IsSolution]

/-- Concatenating the two constraint lists forms the conjunction of two systems. -/
def append (S T : EqIneqSystem X A) : EqIneqSystem X A :=
  ⟨S.eqs ++ T.eqs, S.ineqs ++ T.ineqs⟩

/-- Appending systems concatenates their equations. -/
@[simp] theorem eqs_append (S T : EqIneqSystem X A) :
    (S.append T).eqs = S.eqs ++ T.eqs := by rfl

/-- Appending systems concatenates their inequations. -/
@[simp] theorem ineqs_append (S T : EqIneqSystem X A) :
    (S.append T).ineqs = S.ineqs ++ T.ineqs := by rfl

@[simp] theorem isSolution_append (S T : EqIneqSystem X A) (v : X → G) (c : A → G) :
    (S.append T).IsSolution v c ↔ S.IsSolution v c ∧ T.IsSolution v c := by
  simp [IsSolution, append, List.mem_append, or_imp, forall_and, and_assoc,
    and_left_comm]

/-- Evaluation commutes with a group homomorphism when the variables and coefficients are
mapped along that homomorphism. -/
theorem comp_eval (φ : G →* H) (v : X → G) (c : A → G) :
    φ.comp (eval v c) = eval (φ ∘ v) (φ ∘ c) := by
  apply MonoidHom.ext
  intro w
  apply FreeGroup.lift_unique
  intro i
  cases i <;> simp [eval, Function.comp_def]

/-- Equations remain solved after any group homomorphism. -/
theorem eval_comp_eq_one (S : EqIneqSystem X A) (φ : G →* H)
    (v : X → G) (c : A → G) (h : ∀ w ∈ S.eqs, eval v c w = 1) :
    ∀ w ∈ S.eqs, eval (φ ∘ v) (φ ∘ c) w = 1 := by
  intro w hw
  rw [← comp_eval]
  simp [h w hw]

/-- Injective group homomorphisms preserve and reflect solutions, including inequations. -/
theorem isSolution_comp_iff_of_injective (S : EqIneqSystem X A) (φ : G →* H)
    (hφ : Function.Injective φ) (v : X → G) (c : A → G) :
    S.IsSolution (φ ∘ v) (φ ∘ c) ↔ S.IsSolution v c := by
  simp only [IsSolution, ← comp_eval, MonoidHom.coe_comp, Function.comp_apply,
    map_eq_one_iff φ hφ, ne_eq]

/-- A coefficient-preserving embedding can be used with a separately named coefficient map
in the target. -/
theorem isSolution_comp_iff_of_injective_coeff (S : EqIneqSystem X A) (φ : G →* H)
    (hφ : Function.Injective φ) (v : X → G) (c : A → G) (d : A → H)
    (hd : ∀ a, φ (c a) = d a) :
    S.IsSolution (φ ∘ v) d ↔ S.IsSolution v c := by
  have hcd : φ ∘ c = d := funext hd
  rw [← hcd]
  exact S.isSolution_comp_iff_of_injective φ hφ v c

/-- In a free group, equations have empty reduced words and inequations have nonempty
reduced words. -/
theorem isSolution_iff_toWord {B : Type*} [DecidableEq B]
    (S : EqIneqSystem X A) (v : X → FreeGroup B) (c : A → FreeGroup B) :
    S.IsSolution v c ↔
      (∀ w ∈ S.eqs, (eval v c w).toWord = []) ∧
      (∀ w ∈ S.ineqs, (eval v c w).toWord ≠ []) := by
  simp only [IsSolution, FreeGroup.toWord_eq_nil_iff, ne_eq]

/-- The inequation `x ≠ 1` given by a single variable letter excludes the identity assignment. -/
theorem not_isSolution_one_singleton_ineq (x : X) (c : A → G) :
    ¬ (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).IsSolution
      (fun _ => (1 : G)) c := by
  simp [IsSolution]

/-- A nontrivial value of a variable satisfies the corresponding one-word inequation. -/
theorem isSolution_singleton_ineq_of_ne_one (x : X) (v : X → G) (c : A → G)
    (hx : v x ≠ 1) :
    (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).IsSolution v c := by
  simpa [IsSolution] using hx

open scoped commutatorElement
/-- In a free group, assigning `x = a` and `y = a²` solves the equation that `x` and `y`
commute together with the inequation `x ≠ 1`. -/
theorem isSolution_commutator_of_pow :
    (⟨[⁅FreeGroup.of (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2),
        FreeGroup.of (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)⁆],
      [FreeGroup.of (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)]⟩ :
      EqIneqSystem (Fin 2) (Fin 2)).IsSolution
      (fun i => if i = 0 then FreeGroup.of (0 : Fin 2) else FreeGroup.of (0 : Fin 2) ^ 2)
      FreeGroup.of := by
  simp [IsSolution, eval, map_commutatorElement,
    commutatorElement_eq_one_iff_commute, FreeGroup.of_ne_one]

end EqIneqSystem

end TauCeti.FreeGroup
