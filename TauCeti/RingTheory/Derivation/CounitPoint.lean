/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.RingTheory.Derivation.DualNumber

/-!
# The tangent space at the identity point

For a commutative bialgebra `A` over `R` — the coordinate ring of an affine monoid
scheme — the identity `B`-point of the functor of points is the composite of the counit
with the structure map `R → B`. This file packages `B` as an `A`-algebra through that
point (`Bialgebra.CounitPoint`), so that the dual-number dictionary
`TauCeti.derivationToDualNumberEquivLift` applies verbatim: derivations of `A` at the
identity point — the tangent space at the identity of the reductive-groups roadmap's
Layer 2, the underlying module of `Lie (Spec A)` — are the dual-number points lying
over the identity.

The synonym is a fresh scope for the point-induced algebra structure, as the dictionary
requires; it does not install instances on `B` itself.
-/

public section

namespace TauCeti

open Bialgebra Coalgebra

section BialgebraPoint

variable (R A B : Type*) [CommSemiring R] [CommSemiring A] [Bialgebra R A]
  [CommSemiring B] [Algebra R B]

/-- The identity `B`-point of the functor of points of a bialgebra `A` over `R`: the
counit followed by the structure map of `B`. On an affine monoid scheme this is the
unit element of the monoid of `B`-points. -/
noncomputable def Bialgebra.identityPoint : A →ₐ[R] B :=
  (Algebra.ofId R B).comp (counitAlgHom R A)

/-- Type synonym: `B` as an `A`-algebra through the identity point of the functor of
points. Derivations of `A` valued in `Bialgebra.CounitPoint R A B` are the tangent
vectors at the identity. -/
@[expose]
def Bialgebra.CounitPoint (_R _A : Type*) (B : Type*) : Type _ := B

namespace Bialgebra.CounitPoint

instance : CommSemiring (CounitPoint R A B) := inferInstanceAs (CommSemiring B)

instance : Algebra R (CounitPoint R A B) := inferInstanceAs (Algebra R B)

noncomputable instance : Algebra A (CounitPoint R A B) :=
  (identityPoint R A B).toRingHom.toAlgebra

noncomputable instance : IsScalarTower R A (CounitPoint R A B) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R B r = identityPoint R A B (algebraMap R A r)
    simp [identityPoint]

@[simp]
lemma algebraMap_apply (a : A) :
    algebraMap A (CounitPoint R A B) a = algebraMap R B (counit a) := by
  change identityPoint R A B a = _
  simp [identityPoint]

end Bialgebra.CounitPoint

/-- The tangent space at the identity: derivations of `A` at the identity point are
equivalent to dual-number points of `A` lying over the identity point. This is
`derivationToDualNumberEquivLift` instantiated at the counit. -/
noncomputable def derivationCounitEquivDualNumberLift :
    Derivation R A (Bialgebra.CounitPoint R A B) ≃
      {ψ : A →ₐ[R] DualNumber (Bialgebra.CounitPoint R A B) //
        (TrivSqZeroExt.fstHom R _ _).comp ψ =
          IsScalarTower.toAlgHom R A (Bialgebra.CounitPoint R A B)} :=
  derivationToDualNumberEquivLift R A (Bialgebra.CounitPoint R A B)

end BialgebraPoint

/-- Mirror of `Coalgebra.sum_counit_smul`: summing the counit of the right factors
against the left factors of a comultiplication representative recovers the element. -/
private lemma sum_smul_counit {R C : Type*} [CommSemiring R] [AddCommMonoid C]
    [Module R C] [Coalgebra R C] {c : C} {ι : Type*} (𝓡 : Coalgebra.Repr R c ι) :
    ∑ x ∈ 𝓡.index, Coalgebra.counit (R := R) (𝓡.right x) • 𝓡.left x = c := by
  simpa only [map_sum, TensorProduct.lift.tmul, LinearMap.flip_apply, LinearMap.lsmul_apply,
    one_smul] using congr(TensorProduct.lift (LinearMap.lsmul R C).flip
      $(Coalgebra.sum_tmul_counit_eq (R := R) 𝓡))

section Hopf

open TrivSqZeroExt WithConv Bialgebra Bialgebra.CounitPoint

variable (R A B : Type*) [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
  [CommSemiring B] [Algebra R B]

/-- The augmentation of the dual-number points at the counit point: evaluation of the
classical component, as a homomorphism of convolution groups. Its kernel is the
tangent space at the identity, with its group structure. -/
noncomputable def dualNumberAugmentation :
    WithConv (A →ₐ[R] DualNumber (CounitPoint R A B)) →*
      WithConv (A →ₐ[R] CounitPoint R A B) :=
  AlgHom.mapValue (fstHom R (CounitPoint R A B) (CounitPoint R A B))

variable {R A B}

private lemma toAlgHom_eq_convOne :
    IsScalarTower.toAlgHom R A (CounitPoint R A B) =
      (1 : WithConv (A →ₐ[R] CounitPoint R A B)).ofConv := by
  ext a
  exact (algebraMap_apply R A B a).trans (AlgHom.convOne_apply a).symm

private lemma fst_apply_of_mem_ker {ψ : WithConv (A →ₐ[R] DualNumber (CounitPoint R A B))}
    (h : ψ ∈ (dualNumberAugmentation R A B).ker) (x : A) :
    fst (R := CounitPoint R A B) (ψ.ofConv x) =
      algebraMap R (Bialgebra.CounitPoint R A B) (counit x) := by
  have h' := MonoidHom.mem_ker.mp h
  have := congr($(h').ofConv x)
  simpa [dualNumberAugmentation, AlgHom.mapValue, fstHom_apply, AlgHom.convOne_apply]
    using this

/-- On kernel elements, convolution multiplication adds infinitesimal components: the
group law of the tangent space is addition of derivations. -/
private lemma snd_convMul_apply {ψ₁ ψ₂ : WithConv (A →ₐ[R] DualNumber (CounitPoint R A B))}
    (h₁ : ψ₁ ∈ (dualNumberAugmentation R A B).ker)
    (h₂ : ψ₂ ∈ (dualNumberAugmentation R A B).ker) (a : A) :
    snd (R := CounitPoint R A B) ((ψ₁ * ψ₂).ofConv a) =
      snd (R := CounitPoint R A B) (ψ₁.ofConv a) +
        snd (R := CounitPoint R A B) (ψ₂.ofConv a) := by
  classical
  have key : (ψ₁ * ψ₂).ofConv a =
      ∑ i ∈ (ℛ R a).index, ψ₁.ofConv ((ℛ R a).left i) * ψ₂.ofConv ((ℛ R a).right i) :=
    (ℛ R a).convMul_apply (toConv ψ₁.ofConv.toLinearMap) (toConv ψ₂.ofConv.toLinearMap)
  rw [key, snd_sum]
  have expand : ∀ i ∈ (ℛ R a).index,
      snd (R := CounitPoint R A B) (ψ₁.ofConv ((ℛ R a).left i) * ψ₂.ofConv ((ℛ R a).right i)) =
        counit (R := R) ((ℛ R a).left i) • snd (R := CounitPoint R A B)
            (ψ₂.ofConv ((ℛ R a).right i)) +
          counit (R := R) ((ℛ R a).right i) • snd (R := CounitPoint R A B)
            (ψ₁.ofConv ((ℛ R a).left i)) := by
    intro i _
    rw [snd_mul, fst_apply_of_mem_ker h₁, fst_apply_of_mem_ker h₂, op_smul_eq_smul,
      algebraMap_smul, algebraMap_smul]
  rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, add_comm]
  congr 1
  · calc ∑ i ∈ (ℛ R a).index, counit (R := R) ((ℛ R a).right i) •
          snd (R := CounitPoint R A B) (ψ₁.ofConv ((ℛ R a).left i))
        = snd (R := CounitPoint R A B) (ψ₁.ofConv
            (∑ i ∈ (ℛ R a).index, counit (R := R) ((ℛ R a).right i) • (ℛ R a).left i)) := by
          simp [map_sum, map_smul, snd_sum, snd_smul]
      _ = _ := by rw [sum_smul_counit]
  · calc ∑ i ∈ (ℛ R a).index, counit (R := R) ((ℛ R a).left i) •
          snd (R := CounitPoint R A B) (ψ₂.ofConv ((ℛ R a).right i))
        = snd (R := CounitPoint R A B) (ψ₂.ofConv
            (∑ i ∈ (ℛ R a).index, counit (R := R) ((ℛ R a).left i) • (ℛ R a).right i)) := by
          simp [map_sum, map_smul, snd_sum, snd_smul]
      _ = _ := by rw [Coalgebra.sum_counit_smul]

end Hopf

end TauCeti
