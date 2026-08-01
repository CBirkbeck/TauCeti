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
scheme — the identity `B`-point of the functor of points is the unit of the convolution
monoid, `(1 : WithConv (A →ₐ[R] B)).ofConv`. This file packages `B` as an `A`-algebra
through that point (`Bialgebra.CounitPoint`), so that the dual-number dictionary
`TauCeti.derivationToDualNumberEquivLift` applies verbatim: derivations of `A` at the
identity point — the tangent space at the identity of the reductive-groups roadmap's
Layer 2, the underlying module of `Lie (Spec A)` — are the dual-number points lying
over the identity.

The synonym is a fresh scope for the point-induced algebra structure, as the dictionary
requires; it does not install instances on `B` itself.
-/

public section

namespace TauCeti

open Bialgebra Coalgebra WithConv

section BialgebraPoint

variable (R A B : Type*) [CommSemiring R] [CommSemiring A] [Bialgebra R A]
  [CommSemiring B] [Algebra R B]

/-- Type synonym: `B` as an `A`-algebra through the identity point of the functor of
points. Derivations of `A` valued in `Bialgebra.CounitPoint R A B` are the tangent
vectors at the identity. -/
@[expose]
def Bialgebra.CounitPoint (_R _A : Type*) (B : Type*) : Type _ := B

namespace Bialgebra.CounitPoint

instance : CommSemiring (CounitPoint R A B) := inferInstanceAs (CommSemiring B)

instance : Algebra R (CounitPoint R A B) := inferInstanceAs (Algebra R B)

noncomputable instance : Algebra A (CounitPoint R A B) :=
  ((1 : WithConv (A →ₐ[R] B)).ofConv).toRingHom.toAlgebra

noncomputable instance : IsScalarTower R A (CounitPoint R A B) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R B r = (1 : WithConv (A →ₐ[R] B)).ofConv (algebraMap R A r)
    simp

@[simp]
lemma algebraMap_apply (a : A) :
    algebraMap A (CounitPoint R A B) a = algebraMap R B (counit a) := by
  change (1 : WithConv (A →ₐ[R] B)).ofConv a = _
  simp [AlgHom.convOne_apply]

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
against the left factors of a comultiplication representative recovers the element.
Mathlib has the left identity in both forms (`Coalgebra.sum_counit_smul`, point-free
`Coalgebra.lift_lsmul_comp_counit_comp_comul`, sending `x ⊗ y` to `ε x • y`); this
right identity `∑ ε (a₂) • a₁ = a` exists in neither form there and is derived from
the closest mirror, `Coalgebra.sum_tmul_counit_eq`. -/
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

variable (R A B) in
/-- The tangent subgroup: dual-number points of `A` lying over the identity point, as
the kernel of the augmentation inside the convolution group. -/
noncomputable def tangentKer :
    Subgroup (WithConv (A →ₐ[R] DualNumber (Bialgebra.CounitPoint R A B))) :=
  (dualNumberAugmentation R A B).ker


private lemma toAlgHom_eq_convOne :
    IsScalarTower.toAlgHom R A (CounitPoint R A B) =
      (1 : WithConv (A →ₐ[R] CounitPoint R A B)).ofConv := by
  ext a
  exact (algebraMap_apply R A B a).trans (AlgHom.convOne_apply a).symm

private lemma fst_apply_of_mem_ker {ψ : WithConv (A →ₐ[R] DualNumber (CounitPoint R A B))}
    (h : ψ ∈ tangentKer R A B) (x : A) :
    fst (R := CounitPoint R A B) (ψ.ofConv x) =
      algebraMap R (Bialgebra.CounitPoint R A B) (counit x) := by
  rw [tangentKer, MonoidHom.mem_ker] at h
  have := congr($(h).ofConv x)
  simpa [dualNumberAugmentation, AlgHom.mapValue, fstHom_apply, AlgHom.convOne_apply]
    using this

/-- On kernel elements, convolution multiplication adds infinitesimal components: the
group law of the tangent space is addition of derivations. -/
private lemma snd_convMul_apply {ψ₁ ψ₂ : WithConv (A →ₐ[R] DualNumber (CounitPoint R A B))}
    (h₁ : ψ₁ ∈ tangentKer R A B)
    (h₂ : ψ₂ ∈ tangentKer R A B) (a : A) :
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

private lemma toConv_mem_ker_iff {ψ₀ : A →ₐ[R] DualNumber (Bialgebra.CounitPoint R A B)} :
    toConv ψ₀ ∈ tangentKer R A B ↔
      (fstHom R _ _).comp ψ₀ =
        IsScalarTower.toAlgHom R A (Bialgebra.CounitPoint R A B) := by
  rw [tangentKer, MonoidHom.mem_ker, toAlgHom_eq_convOne]
  exact ⟨fun h => congrArg ofConv h, fun h => ofConv_injective h⟩

variable (R A B) in
/-- The group of the tangent space at the identity: the kernel of the dual-number
augmentation is, additively, the derivations at the identity point. Convolution of
dual-number points over the identity corresponds to addition of derivations — the
underlying additive group of `Lie (Spec A)` evaluated on `B`. -/
noncomputable def derivationMulEquivAugmentationKer :
    Multiplicative (Derivation R A (Bialgebra.CounitPoint R A B)) ≃*
      tangentKer R A B where
  toFun d := ⟨toConv (derivationCounitEquivDualNumberLift R A B d.toAdd).1,
    toConv_mem_ker_iff.mpr (derivationCounitEquivDualNumberLift R A B d.toAdd).2⟩
  invFun ψ := .ofAdd <| (derivationCounitEquivDualNumberLift R A B).symm
    ⟨ψ.1.ofConv, toConv_mem_ker_iff.mp ψ.2⟩
  left_inv d := by
    exact congrArg Multiplicative.ofAdd <|
      (derivationCounitEquivDualNumberLift R A B).symm_apply_apply d.toAdd
  right_inv ψ := by
    have h := (derivationCounitEquivDualNumberLift R A B).apply_symm_apply
      ⟨ψ.1.ofConv, toConv_mem_ker_iff.mp ψ.2⟩
    rw [Subtype.ext_iff] at h
    exact Subtype.ext ((congrArg toConv h).trans (toConv_ofConv ψ.1))
  map_mul' d₁ d₂ := by
    have h₁ := toConv_mem_ker_iff.mpr (derivationCounitEquivDualNumberLift R A B d₁.toAdd).2
    have h₂ := toConv_mem_ker_iff.mpr (derivationCounitEquivDualNumberLift R A B d₂.toAdd).2
    have hprod := toConv_mem_ker_iff.mpr
      (derivationCounitEquivDualNumberLift R A B (d₁.toAdd + d₂.toAdd)).2
    refine Subtype.ext (ofConv_injective (AlgHom.ext fun a => TrivSqZeroExt.ext ?_ ?_))
    · exact (fst_apply_of_mem_ker hprod a).trans
        (fst_apply_of_mem_ker (mul_mem h₁ h₂) a).symm
    · simp only [MulMemClass.mk_mul_mk]
      rw [snd_convMul_apply h₁ h₂ a]
      simp [derivationCounitEquivDualNumberLift]

end Hopf

end TauCeti
