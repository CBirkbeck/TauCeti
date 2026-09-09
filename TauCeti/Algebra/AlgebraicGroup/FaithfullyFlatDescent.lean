/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Faithfully flat descent for the functor of points

Let `A → B` be a faithfully flat extension of commutative `R`-algebras. The two maps
`B ⇉ B ⊗[A] B` give two restriction maps on the `B`-points represented by a Hopf algebra `H`.
This file proves that the `A`-points are exactly the `B`-points on which those restrictions agree,
as an equivalence of groups. The coordinate algebra need not be commutative for this algebraic
descent statement; the affine-group-scheme application specializes to commutative `H`.

The proof uses Mathlib's effective-descent theorem
`Algebra.IsEffective.of_faithfullyFlat`: the equalizer of
`B ⇉ B ⊗[A] B` is the image of `A`. Rather than repeating its elementwise argument for
points, we package that equalizer as an algebra equivalence and precompose algebra maps out of
`H`. The resulting equivalence respects convolution because it is induced by postcomposition in
the value algebra.

This is the affine, group-valued faithfully flat descent statement needed by the fppf sheaf and
quotient lane of the reductive-groups roadmap. The finite-presentation part of an fppf cover is
not needed for descent itself, so the result is stated at the natural faithfully flat level.

## Main declarations

* `AlgHom.descentSubgroup`: the subgroup of `B`-points satisfying the
  equalizer condition over `B ⊗[A] B`.
* `AlgHom.faithfullyFlatDescentMulEquiv`: `A`-points are equivalent to that descent
  subgroup.

## References

This is the affine representable case of faithfully flat descent. The algebraic input is
Mathlib's `Algebra.IsEffective.of_faithfullyFlat`, following the standard Amitsur equalizer
`A → B ⇉ B ⊗[A] B`.
-/

public section

open Algebra.TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti

section

universe u v w x

variable {R : Type u} {H : Type v} (A : Type w) (B : Type x)
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]

section CommSemiring

variable [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra A B]
variable [IsScalarTower R A B]

private noncomputable def _root_.AlgHom.faithfullyFlatDescentLeft : B →ₐ[R] (B ⊗[A] B) :=
  (includeLeft : B →ₐ[A] (B ⊗[A] B)).restrictScalars R

private noncomputable def _root_.AlgHom.faithfullyFlatDescentRight : B →ₐ[R] (B ⊗[A] B) :=
  (includeRight : B →ₐ[A] (B ⊗[A] B)).restrictScalars R

/-- The subgroup of `B`-points satisfying the descent equalizer condition along `A → B`.

A point `f : H →ₐ[R] B` belongs to this subgroup exactly when its two postcompositions
`H →ₐ[R] B ⇉ B ⊗[A] B` agree. The subgroup structure comes from functoriality of
convolution in the value algebra. -/
noncomputable def _root_.AlgHom.descentSubgroup :
    Subgroup (WithConv (H →ₐ[R] B)) :=
  MonoidHom.eqLocus
    (AlgHom.mapValue (H := H) (AlgHom.faithfullyFlatDescentLeft (R := R) A (B := B)))
    (AlgHom.mapValue (H := H) (AlgHom.faithfullyFlatDescentRight (R := R) A (B := B)))

private theorem _root_.AlgHom.mem_descentSubgroup_iff_maps (f : WithConv (H →ₐ[R] B)) :
    f ∈ AlgHom.descentSubgroup (R := R) (H := H) A B ↔
      AlgHom.mapValue (H := H) (AlgHom.faithfullyFlatDescentLeft (R := R) A (B := B)) f =
        AlgHom.mapValue (H := H) (AlgHom.faithfullyFlatDescentRight (R := R) A (B := B)) f :=
  Iff.rfl

/-- Pointwise form of the descent equalizer condition. -/
@[simp]
theorem _root_.AlgHom.mem_descentSubgroup_iff_apply (f : WithConv (H →ₐ[R] B)) :
    f ∈ AlgHom.descentSubgroup (R := R) (H := H) A B ↔
      ∀ h, (includeLeft (R := A) (S := A) (A := B) (B := B)) (f h) =
        (includeRight (R := A) (A := B) (B := B)) (f h) := by
  rw [AlgHom.mem_descentSubgroup_iff_maps]
  constructor
  · intro hf h
    exact DFunLike.congr_fun (congr_arg WithConv.ofConv hf) h
  · intro hf
    apply WithConv.toConv_injective
    ext h
    exact hf h

end CommSemiring

section CommRing

variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
variable [IsScalarTower R A B] [Module.FaithfullyFlat A B]

private noncomputable def _root_.AlgHom.descentEqualizerHom :
    A →ₐ[R] AlgHom.equalizer (AlgHom.faithfullyFlatDescentLeft (R := R) A (B := B))
      (AlgHom.faithfullyFlatDescentRight (R := R) A (B := B)) :=
  AlgHom.codRestrict (IsScalarTower.toAlgHom R A B) _ fun a => by
    simp [AlgHom.faithfullyFlatDescentLeft, AlgHom.faithfullyFlatDescentRight, tmul_one_eq_one_tmul]

omit [Module.FaithfullyFlat A B] in
@[simp]
private theorem _root_.AlgHom.descentEqualizerHom_apply_val (a : A) :
    (AlgHom.descentEqualizerHom (R := R) A B a : B) = algebraMap A B a :=
  rfl

omit [Module.FaithfullyFlat A B] in
private theorem _root_.AlgHom.mem_descentEqualizer_iff_eqLocus (b : B) :
    b ∈ AlgHom.equalizer (AlgHom.faithfullyFlatDescentLeft (R := R) A (B := B))
      (AlgHom.faithfullyFlatDescentRight (R := R) A (B := B)) ↔
        b ∈ includeLeftRingHom.eqLocus includeRight.toRingHom (S := B ⊗[A] B) :=
  by
    rw [AlgHom.mem_equalizer, RingHom.mem_eqLocus]
    simp only [AlgHom.faithfullyFlatDescentLeft, AlgHom.faithfullyFlatDescentRight,
      AlgHom.restrictScalars_apply, includeLeft_apply, includeLeftRingHom_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, includeRight_apply]

private theorem _root_.AlgHom.descentEqualizerHom_bijective :
    Function.Bijective (AlgHom.descentEqualizerHom (R := R) A B) := by
  constructor
  · intro a b hab
    apply FaithfulSMul.algebraMap_injective A B
    simpa only [AlgHom.descentEqualizerHom_apply_val] using congr_arg Subtype.val hab
  · rintro ⟨b, hb⟩
    have hb' :
        b ∈ includeLeftRingHom.eqLocus includeRight.toRingHom (S := B ⊗[A] B) :=
      (AlgHom.mem_descentEqualizer_iff_eqLocus (R := R) A B b).mp hb
    have hb'' : b ∈ Set.range (algebraMap A B) := by
      rw [← Algebra.IsEffective.eqLocus_includeLeft_includeRight
        (Algebra.IsEffective.of_faithfullyFlat A B)]
      exact hb'
    obtain ⟨a, ha⟩ := hb''
    refine ⟨a, Subtype.ext ?_⟩
    simpa only [AlgHom.descentEqualizerHom_apply_val] using ha

private noncomputable def _root_.AlgHom.descentEqualizerEquiv :
    A ≃ₐ[R] AlgHom.equalizer (AlgHom.faithfullyFlatDescentLeft (R := R) A (B := B))
      (AlgHom.faithfullyFlatDescentRight (R := R) A (B := B)) :=
  AlgEquiv.ofBijective (AlgHom.descentEqualizerHom (R := R) A B)
    (AlgHom.descentEqualizerHom_bijective (R := R) A B)

@[simp]
private theorem _root_.AlgHom.descentEqualizerEquiv_apply_val (a : A) :
    (AlgHom.descentEqualizerEquiv (R := R) A B a : B) = algebraMap A B a := by
  rw [AlgHom.descentEqualizerEquiv, AlgEquiv.ofBijective_apply]
  exact AlgHom.descentEqualizerHom_apply_val (R := R) A B a

private noncomputable def _root_.AlgHom.faithfullyFlatDescentHom :
    WithConv (H →ₐ[R] A) →* AlgHom.descentSubgroup (R := R) (H := H) A B :=
  (AlgHom.mapValue (H := H) (IsScalarTower.toAlgHom R A B)).codRestrict _ fun f => by
    rw [AlgHom.mem_descentSubgroup_iff_apply]
    intro h
    simp

omit [Module.FaithfullyFlat A B] in
private theorem _root_.AlgHom.faithfullyFlatDescentHom_apply (f : WithConv (H →ₐ[R] A)) :
    (AlgHom.faithfullyFlatDescentHom (R := R) (H := H) A B f : WithConv (H →ₐ[R] B)) =
      AlgHom.mapValue (H := H) (IsScalarTower.toAlgHom R A B) f :=
  rfl

omit [Module.FaithfullyFlat A B] in
@[simp]
private theorem _root_.AlgHom.faithfullyFlatDescentHom_apply_apply (f : WithConv (H →ₐ[R] A))
    (h : H) :
    (AlgHom.faithfullyFlatDescentHom (R := R) (H := H) A B f :
      AlgHom.descentSubgroup (R := R) (H := H) A B).1.ofConv h =
        algebraMap A B (f.ofConv h) := by
  rw [AlgHom.faithfullyFlatDescentHom_apply, AlgHom.mapValue_apply, toConv_ofConv]
  rfl

private theorem _root_.AlgHom.faithfullyFlatDescentHom_bijective :
    Function.Bijective (AlgHom.faithfullyFlatDescentHom (R := R) (H := H) A B) := by
  constructor
  · intro f g hfg
    apply WithConv.ofConv_injective
    ext h
    apply FaithfulSMul.algebraMap_injective A B
    simpa only [AlgHom.faithfullyFlatDescentHom_apply_apply] using
      congr_arg (fun p : AlgHom.descentSubgroup (R := R) (H := H) A B => p.1.ofConv h) hfg
  · intro f
    let f' : H →ₐ[R]
        AlgHom.equalizer (AlgHom.faithfullyFlatDescentLeft (R := R) A (B := B))
          (AlgHom.faithfullyFlatDescentRight (R := R) A (B := B)) :=
      AlgHom.codRestrict f.1.ofConv _ fun h =>
        (AlgHom.mem_descentSubgroup_iff_apply (R := R) A B f.1).mp f.2 h
    let g : H →ₐ[R] A := (AlgHom.descentEqualizerEquiv (R := R) A B).symm.toAlgHom.comp f'
    refine ⟨toConv g, Subtype.ext ?_⟩
    apply WithConv.ofConv_injective
    ext h
    rw [AlgHom.faithfullyFlatDescentHom_apply_apply, ofConv_toConv]
    have hg : g h = (AlgHom.descentEqualizerEquiv (R := R) A B).symm (f' h) := by
      exact AlgHom.comp_apply _ _ h
    rw [hg]
    have hdesc :=
      congr_arg Subtype.val ((AlgHom.descentEqualizerEquiv (R := R) A B).apply_symm_apply (f' h))
    rw [AlgHom.descentEqualizerEquiv_apply_val] at hdesc
    have hf' : (f' h : B) = f.1.ofConv h := by
      dsimp only [f']
      exact AlgHom.coe_codRestrict f.1.ofConv _ _ h
    rw [hf'] at hdesc
    exact hdesc

/-- **Faithfully flat descent for affine group-valued points.** If `B` is faithfully flat over
`A`, base change identifies the convolution group of `A`-points of `H` with the subgroup of
`B`-points whose two restrictions to `B ⊗[A] B` agree. -/
noncomputable def _root_.AlgHom.faithfullyFlatDescentMulEquiv :
    WithConv (H →ₐ[R] A) ≃* AlgHom.descentSubgroup (R := R) (H := H) A B :=
  MulEquiv.ofBijective (AlgHom.faithfullyFlatDescentHom (R := R) (H := H) A B)
    (AlgHom.faithfullyFlatDescentHom_bijective (R := R) (H := H) A B)

/-- The faithfully flat descent equivalence sends an `A`-point to its base change to `B`. -/
@[simp]
theorem _root_.AlgHom.faithfullyFlatDescentMulEquiv_apply (f : WithConv (H →ₐ[R] A)) :
    (AlgHom.faithfullyFlatDescentMulEquiv (R := R) (H := H) A B f : WithConv (H →ₐ[R] B)) =
      AlgHom.mapValue (H := H) (IsScalarTower.toAlgHom R A B) f :=
  by
    rw [AlgHom.faithfullyFlatDescentMulEquiv, MulEquiv.ofBijective_apply]
    exact AlgHom.faithfullyFlatDescentHom_apply (R := R) A B f

/-- Descending a compatible `B`-point and extending it back to `B` recovers the original
point. -/
@[simp]
theorem _root_.AlgHom.mapValue_faithfullyFlatDescentMulEquiv_symm_apply
    (f : AlgHom.descentSubgroup (R := R) (H := H) A B) :
    WithConv.toConv ((IsScalarTower.toAlgHom R A B).comp
      ((AlgHom.faithfullyFlatDescentMulEquiv (R := R) (H := H) A B).symm f).ofConv) = f.1 := by
  rw [← AlgHom.mapValue_apply]
  rw [← AlgHom.faithfullyFlatDescentMulEquiv_apply]
  exact congr_arg Subtype.val
    ((AlgHom.faithfullyFlatDescentMulEquiv (R := R) (H := H) A B).apply_symm_apply f)

end CommRing

end

end TauCeti
