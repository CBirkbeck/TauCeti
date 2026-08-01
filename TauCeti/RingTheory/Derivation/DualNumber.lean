/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.Derivation.ToSquareZero

/-!
# Dual-number points and derivations

An `R`-algebra homomorphism `A →ₐ[R] B[ε]` into the dual numbers lifting a fixed point
`A →ₐ[R] B` is the same data as an `R`-derivation of `A` valued in `B`. This is the
infinitesimal-lifting dictionary specialised to the square-zero extension `B[ε] → B`,
and it is the engine identifying the tangent space of a functor of points with a module
of derivations (reductive-groups roadmap, Layer 2): tangent vectors at a point are
exactly the dual-number points lying over it.

The fixed point is carried by the algebra-tower hypotheses `[Algebra A B]`
`[IsScalarTower R A B]`, as in `Mathlib.RingTheory.Derivation.ToSquareZero`; for an
arbitrary point `φ : A →ₐ[R] B`, instantiate the tower with `φ.toRingHom.toAlgebra`.

## Main declarations

* `derivationEquivDualNumberLift`: `R`-derivations `A → B` are equivalent to lifts
  `A →ₐ[R] B[ε]` of the structure point along `TrivSqZeroExt.fstHom`.
-/

public section

namespace TauCeti

open TrivSqZeroExt

variable (R A B : Type*) [CommSemiring R] [CommSemiring A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The square-zero kernel ideal of `B[ε] → B` is linearly equivalent to `B`, by taking
the infinitesimal component. -/
noncomputable def kerIdealLinearEquiv : (kerIdeal B B : Ideal (DualNumber B)) ≃ₗ[B] B where
  toFun x := (x : DualNumber B).snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun b := ⟨TrivSqZeroExt.inr b, by simp [mem_kerIdeal_iff_inr]⟩
  left_inv x := Subtype.ext ((mem_kerIdeal_iff_inr _ _ _).mp x.2).symm
  right_inv b := rfl

variable {R A B} in
/-- A dual-number point lifts the structure point through the quotient by the kernel
ideal exactly when it lifts it through the infinitesimal augmentation. -/
private lemma comp_mkₐ_eq_iff_comp_fstHom_eq (ψ : A →ₐ[R] DualNumber B) :
    (Ideal.Quotient.mkₐ R (kerIdeal B B)).comp ψ =
        IsScalarTower.toAlgHom R A (DualNumber B ⧸ kerIdeal B B) ↔
      (fstHom R B B).comp ψ = IsScalarTower.toAlgHom R A B := by
  rw [AlgHom.ext_iff, AlgHom.ext_iff]
  refine forall_congr' fun a => ?_
  have hq : IsScalarTower.toAlgHom R A (DualNumber B ⧸ kerIdeal B B) a =
      Ideal.Quotient.mk (kerIdeal B B) (IsScalarTower.toAlgHom R A (DualNumber B) a) := by
    rw [IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom',
      IsScalarTower.algebraMap_apply A (DualNumber B) (DualNumber B ⧸ kerIdeal B B),
      Ideal.Quotient.algebraMap_eq]
  rw [AlgHom.coe_comp, AlgHom.coe_comp, Function.comp_apply, Function.comp_apply,
    Ideal.Quotient.mkₐ_eq_mk, hq, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  change _ ∈ RingHom.ker (fstHom B B B) ↔ _
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  simp [IsScalarTower.coe_toAlgHom', algebraMap_eq_inl']

/-- Lifting the structure point of an algebra to the dual numbers is the same as giving
a derivation: the equivalence between `R`-derivations `A → B` and dual-number points
`A →ₐ[R] B[ε]` lying over the point `A →ₐ[R] B` of the tower. -/
noncomputable def derivationEquivDualNumberLift :
    Derivation R A B ≃
      {ψ : A →ₐ[R] DualNumber B // (fstHom R B B).comp ψ = IsScalarTower.toAlgHom R A B} :=
  (((kerIdealLinearEquiv B).restrictScalars A).compDer.symm.toEquiv).trans <|
    (derivationToSquareZeroEquivLift (kerIdeal B B) (kerIdeal_sq B B)).trans <|
      Equiv.subtypeEquiv (Equiv.refl _) fun ψ => comp_mkₐ_eq_iff_comp_fstHom_eq ψ

end TauCeti
