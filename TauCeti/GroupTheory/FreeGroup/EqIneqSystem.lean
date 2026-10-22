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

namespace FreeGroup

/-- A finite conjunction of equations and inequations in variables `X` with coefficient
letters `A`. The lists need not be deduplicated: they are finite syntax, and their order has
no effect on solutions. -/
structure EqIneqSystem (X A : Type*) where
  /-- Words required to evaluate to the identity. -/
  eqs : List (FreeGroup (X ⊕ A))
  /-- Words required to evaluate away from the identity. -/
  ineqs : List (FreeGroup (X ⊕ A))

namespace EqIneqSystem

variable {X A : Type*} {G H : Type*} [Group G] [Group H]

/-- Evaluation of a word under a variable assignment and a coefficient map. -/
def eval (v : X → G) (c : A → G) : FreeGroup (X ⊕ A) →* G :=
  FreeGroup.lift (Sum.elim v c)

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

theorem isSolution_iff (S : EqIneqSystem X A) (v : X → G) (c : A → G) :
    S.IsSolution v c ↔
      (∀ w ∈ S.eqs, eval v c w = 1) ∧ (∀ w ∈ S.ineqs, eval v c w ≠ 1) :=
  Iff.rfl

/-- The empty system places no conditions on an assignment. -/
def empty (X A : Type*) : EqIneqSystem X A := ⟨[], []⟩

@[simp] theorem isSolution_empty (v : X → G) (c : A → G) :
    (empty X A).IsSolution v c := by
  simp [empty, IsSolution]

/-- Concatenating the two constraint lists forms the conjunction of two systems. -/
def append (S T : EqIneqSystem X A) : EqIneqSystem X A :=
  ⟨S.eqs ++ T.eqs, S.ineqs ++ T.ineqs⟩

@[simp] theorem isSolution_append (S T : EqIneqSystem X A) (v : X → G) (c : A → G) :
    (S.append T).IsSolution v c ↔ S.IsSolution v c ∧ T.IsSolution v c := by
  simp [IsSolution, append, List.mem_append, or_imp, forall_and, and_assoc,
    and_left_comm]

/-- Evaluation commutes with a group homomorphism when the variables and coefficients are
mapped along that homomorphism. -/
theorem eval_map (φ : G →* H) (v : X → G) (c : A → G) :
    eval (φ ∘ v) (φ ∘ c) = φ.comp (eval v c) := by
  apply MonoidHom.ext
  intro w
  symm
  apply FreeGroup.lift_unique
  intro i
  cases i <;> simp [eval, Function.comp_def]

/-- Equations remain solved after any group homomorphism. -/
theorem equations_map (S : EqIneqSystem X A) (φ : G →* H)
    (v : X → G) (c : A → G) (h : ∀ w ∈ S.eqs, eval v c w = 1) :
    ∀ w ∈ S.eqs, eval (φ ∘ v) (φ ∘ c) w = 1 := by
  intro w hw
  rw [eval_map]
  simp [h w hw]

/-- Injective group homomorphisms preserve and reflect solutions, including inequations. -/
theorem isSolution_map (S : EqIneqSystem X A) (φ : G →* H)
    (hφ : Function.Injective φ) (v : X → G) (c : A → G) :
    S.IsSolution (φ ∘ v) (φ ∘ c) ↔ S.IsSolution v c := by
  simp only [IsSolution, eval_map, MonoidHom.coe_comp, Function.comp_apply]
  simp only [← φ.map_one, hφ.eq_iff, ne_eq]

/-- A coefficient-preserving embedding can be used with a separately named coefficient map
in the target. -/
theorem isSolution_map_coeff (S : EqIneqSystem X A) (φ : G →* H)
    (hφ : Function.Injective φ) (v : X → G) (c : A → G) (d : A → H)
    (hd : ∀ a, φ (c a) = d a) :
    S.IsSolution (φ ∘ v) d ↔ S.IsSolution v c := by
  have hcd : φ ∘ c = d := funext hd
  rw [← hcd]
  exact S.isSolution_map φ hφ v c

/-- For assignments into the coefficient free group, equations have empty reduced words
and inequations have nonempty reduced words. -/
theorem isSolution_iff_reduced [DecidableEq A]
    (S : EqIneqSystem X A) (v : X → FreeGroup A) :
    S.IsSolution v FreeGroup.of ↔
      (∀ w ∈ S.eqs, (eval v FreeGroup.of w).toWord = []) ∧
      (∀ w ∈ S.ineqs, (eval v FreeGroup.of w).toWord ≠ []) := by
  simp only [IsSolution, FreeGroup.toWord_eq_nil_iff, ne_eq]

/-- An inequation in a single variable excludes the identity assignment. -/
theorem not_isSolution_of_ineq_variable (x : X) (c : A → G) :
    ¬ (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).IsSolution
      (fun _ => (1 : G)) c := by
  simp [IsSolution]

/-- A nontrivial value of a variable satisfies the corresponding one-word inequation. -/
theorem isSolution_of_ineq_variable (x : X) (v : X → G) (c : A → G)
    (hx : v x ≠ 1) :
    (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).IsSolution v c := by
  simpa [IsSolution] using hx

/-- The one-word inequation is satisfiable in a free group and excludes its identity
assignment. -/
theorem ineq_variable_nontrivial (x : X) (a : A) :
    (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).IsSolution
      (fun _ => FreeGroup.of a) FreeGroup.of ∧
    ¬ (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).IsSolution
      (fun _ => (1 : FreeGroup A)) FreeGroup.of := by
  exact ⟨isSolution_of_ineq_variable x _ _ (FreeGroup.of_ne_one a),
    not_isSolution_of_ineq_variable x _⟩

open scoped commutatorElement
/-- In a free group, assigning `x = a` and `y = a²` solves the equation that `x` and `y`
commute together with the inequation `x ≠ 1`. -/
theorem solution_commuting :
    (⟨[⁅FreeGroup.of (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 1),
        FreeGroup.of (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 1)⁆],
      [FreeGroup.of (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 1)]⟩ :
      EqIneqSystem (Fin 2) (Fin 1)).IsSolution
      (fun i => if i = 0 then FreeGroup.of (0 : Fin 1) else FreeGroup.of (0 : Fin 1) ^ 2)
      FreeGroup.of := by
  simp [IsSolution, eval, map_commutatorElement,
    commutatorElement_eq_one_iff_commute, FreeGroup.of_ne_one]

end EqIneqSystem

end FreeGroup
