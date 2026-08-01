/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Dual-number points and derivations

An `R`-algebra homomorphism `A →ₐ[R] B[ε]` into the dual numbers lifting a fixed point
`A →ₐ[R] B` is the same data as an `R`-derivation of `A` valued in `B`. This is the
infinitesimal-lifting dictionary specialised to the square-zero extension `B[ε] → B`,
and it is the engine identifying the tangent space of a functor of points with a module
of derivations (reductive-groups roadmap, Layer 2): tangent vectors at a point are
exactly the dual-number points lying over it.

The fixed point is carried by the algebra-tower hypotheses `[Algebra A B]`
`[IsScalarTower R A B]`, as in `Mathlib.RingTheory.Derivation.ToSquareZero`. For an
arbitrary point `φ : A →ₐ[R] B`, instantiate the tower locally with
`letI := φ.toRingHom.toAlgebra` and `IsScalarTower.of_algHom φ` — in a fresh scope
only: installing the instance where an `SMul A B` already exists creates a diamond,
and derivations elaborated before it refer to the old point.

The construction is direct (send `d` to `a ↦ (algebraMap A B a, d a)`), which keeps
`B` a commutative semiring; `Mathlib.RingTheory.Derivation.ToSquareZero` proves the
ideal-general statement but forces a `CommRing`.

## Main declarations

* `derivationEquivDualNumberLift`: `R`-derivations `A → B` are equivalent to lifts
  `A →ₐ[R] B[ε]` of the structure point along `TrivSqZeroExt.fstHom`.
-/

public section

namespace TauCeti

open TrivSqZeroExt

variable (R A B : Type*) [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

variable {A B} in
/-- A derivation extends the structure point of the tower to a dual-number point: the
value at `a` has classical component `algebraMap A B a` and infinitesimal component
`d a`. -/
private def liftOfDerivation (d : Derivation R A B) : A →ₐ[R] DualNumber B where
  toFun a := inl (algebraMap A B a) + inr (d a)
  map_one' := by rw [map_one, d.map_one_eq_zero, inr_zero, add_zero, inl_one]
  map_mul' a b := by
    rw [d.leibniz, map_mul, mul_add, add_mul, add_mul, inl_mul_inl, inl_mul_inr,
      inr_mul_inl, inr_mul_inr, add_zero, Algebra.smul_def, Algebra.smul_def,
      op_smul_eq_smul, smul_eq_mul, smul_eq_mul, inr_add]
    abel
  map_zero' := by rw [map_zero, map_zero, inr_zero, add_zero, inl_zero]
  map_add' a b := by rw [map_add, map_add, inl_add, inr_add]; abel
  commutes' r := by
    rw [Derivation.map_algebraMap, inr_zero, add_zero, ← IsScalarTower.algebraMap_apply,
      algebraMap_eq_inl']

/-- Lifting the structure point of an algebra to the dual numbers is the same as giving
a derivation: the equivalence between `R`-derivations `A → B` and dual-number points
`A →ₐ[R] B[ε]` lying over the point `A →ₐ[R] B` of the tower. -/
noncomputable def derivationEquivDualNumberLift :
    Derivation R A B ≃
      {ψ : A →ₐ[R] DualNumber B // (fstHom R B B).comp ψ = IsScalarTower.toAlgHom R A B} where
  toFun d := ⟨liftOfDerivation R d, by ext a; simp [liftOfDerivation]⟩
  invFun ψ :=
    { toLinearMap := (sndHom B B).restrictScalars R ∘ₗ ψ.1.toLinearMap
      map_one_eq_zero' := by simp [snd_one]
      leibniz' := fun a b => by
        have ha : fst (ψ.1 a) = algebraMap A B a := congrArg (fun f => f a) <|
          congrArg DFunLike.coe ψ.2
        have hb : fst (ψ.1 b) = algebraMap A B b := congrArg (fun f => f b) <|
          congrArg DFunLike.coe ψ.2
        simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
          AlgHom.toLinearMap_apply, map_mul, snd_mul, sndHom_apply, ha, hb, smul_eq_mul,
          op_smul_eq_smul, Algebra.smul_def] }
  left_inv d := by ext a; simp [liftOfDerivation]
  right_inv ψ := by
    ext a
    · have ha : fst (ψ.1 a) = algebraMap A B a := congrArg (fun f => f a) <|
        congrArg DFunLike.coe ψ.2
      simpa [liftOfDerivation] using ha.symm
    · simp [liftOfDerivation]

variable {R A B}

@[simp]
lemma derivationEquivDualNumberLift_apply_fst (d : Derivation R A B) (a : A) :
    fst ((derivationEquivDualNumberLift R A B d : A →ₐ[R] DualNumber B) a) =
      algebraMap A B a := by
  simp [derivationEquivDualNumberLift, liftOfDerivation]

@[simp]
lemma derivationEquivDualNumberLift_apply_snd (d : Derivation R A B) (a : A) :
    snd ((derivationEquivDualNumberLift R A B d : A →ₐ[R] DualNumber B) a) = d a := by
  simp [derivationEquivDualNumberLift, liftOfDerivation]

@[simp]
lemma derivationEquivDualNumberLift_symm_apply
    (ψ : {ψ : A →ₐ[R] DualNumber B //
      (fstHom R B B).comp ψ = IsScalarTower.toAlgHom R A B}) (a : A) :
    (derivationEquivDualNumberLift R A B).symm ψ a = snd (ψ.1 a) := by
  simp [derivationEquivDualNumberLift]

end TauCeti
