/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic

/-!
# The differential of a Hopf-algebra morphism on tangent spaces

A morphism `φ : A' →ₐc[R] A` of Hopf algebras induces, contravariantly on coordinate
rings and hence covariantly on the corresponding affine group schemes `Spec A → Spec A'`,
a map of tangent spaces at the identity: precomposition of dual-number points. The
coefficient algebras `Bialgebra.CounitAlgebra R A B` and `Bialgebra.CounitAlgebra R A' B`
share the carrier `B` and its `R`-algebra structure, and the identity points correspond
under `φ` because bialgebra morphisms intertwine counits; so precomposition restricts to
the tangent kernels.

## Main declarations

* `TauCeti.tangentKerMap`: the differential, as a group homomorphism between tangent
  kernels.
* `TauCeti.tangentKerMap_id` and `TauCeti.tangentKerMap_comp`: functoriality.
-/

public section

namespace TauCeti

open Coalgebra WithConv TrivSqZeroExt

section Differential

variable {R A A' B : Type*} [CommSemiring R]
  [CommSemiring A] [HopfAlgebra R A] [CommSemiring A'] [HopfAlgebra R A']
  [CommSemiring B] [Algebra R B]

/-- The first component of a dual-number element, transported between the two counit
coefficient indexings through their canonical identifications with `B`. The two
`Semiring`/`Algebra R` structures are the same `inferInstanceAs` terms over the shared
carrier, so the transport is the identity, recorded here once as an explicit lemma. -/
private lemma fst_transport (z : DualNumber (Bialgebra.CounitAlgebra R A' B)) :
    fst (R := Bialgebra.CounitAlgebra R A' B) z =
      (Bialgebra.CounitAlgebra.algEquivSelf R A' B).symm
        (Bialgebra.CounitAlgebra.algEquivSelf R A B
          (fst (R := Bialgebra.CounitAlgebra R A B) z)) := by
  rw [Bialgebra.CounitAlgebra.algEquivSelf_symm_apply, Bialgebra.CounitAlgebra.algEquivSelf_apply]
  -- The residual identification of the two indexings of `fst` over the shared carrier
  -- is definitional; this is the single point where it is used.
  rfl

private lemma fst_mapDomain_of_mem_tangentKer (φ : A' →ₐc[R] A)
    {ψ : WithConv (A →ₐ[R] DualNumber (Bialgebra.CounitAlgebra R A B))}
    (hψ : ψ ∈ tangentKer R A B) (a : A') :
    fst (R := Bialgebra.CounitAlgebra R A' B)
        ((AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ ψ).ofConv
          a) =
      algebraMap A' (Bialgebra.CounitAlgebra R A' B) a := by
  rw [mem_tangentKer_iff] at hψ
  have h := congrArg (fun χ : A →ₐ[R] Bialgebra.CounitAlgebra R A B => χ (φ a)) hψ
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h
  -- The cross-index step is the explicit transport lemma `fst_transport`
  -- (`AlgHom.mapDomain_apply_apply` is a `rfl`-lemma, so the argument of `fst` is the
  -- precomposed point); the remaining rewrites stay on one index at a time.
  rw [fst_transport, Bialgebra.CounitAlgebra.algEquivSelf_apply R A B,
    Bialgebra.CounitAlgebra.algEquivSelf_symm_apply R A' B,
    Bialgebra.CounitAlgebra.algebraMap_apply,
    ← CoalgHomClass.counit_comp_apply (F := A' →ₐc[R] A) φ a,
    ← Bialgebra.CounitAlgebra.algebraMap_apply (R := R) (A := A) (B := B)]
  exact h

/-- The differential of a Hopf-algebra morphism on tangent kernels: a morphism
`φ : A' →ₐc[R] A` of Hopf algebras sends a dual-number point of `A` over the identity to
a dual-number point of `A'` over the identity by precomposition. The coefficient
identification `Bialgebra.CounitAlgebra R A B = B = Bialgebra.CounitAlgebra R A' B` is
definitional, and the identity points correspond because `φ` intertwines the counits. -/
noncomputable def tangentKerMap (φ : A' →ₐc[R] A) :
    tangentKer R A B →* tangentKer R A' B :=
  (((AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ).domRestrict
      (tangentKer R A B)).codRestrict (tangentKer R A' B)) fun ψ => by
    rw [mem_tangentKer_iff]
    ext a
    rw [AlgHom.comp_apply]
    exact fst_mapDomain_of_mem_tangentKer φ ψ.2 a

/-- The differential acts by precomposition on dual-number points. -/
@[simp]
lemma tangentKerMap_apply_val (φ : A' →ₐc[R] A) (ψ : tangentKer R A B) :
    (tangentKerMap φ ψ).val =
      AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ ψ.val := by
  -- `tangentKerMap` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly: the value of the corestriction is the
  -- value of `mapDomain` on the inclusion.
  change ((AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ).domRestrict
      (tangentKer R A B)) ψ = _
  rfl

/-- The differential of the identity morphism is the identity. -/
@[simp]
lemma tangentKerMap_id :
    tangentKerMap (B := B) (BialgHom.id R A) = MonoidHom.id (tangentKer R A B) := by
  refine MonoidHom.ext fun ψ => Subtype.ext ?_
  rw [tangentKerMap_apply_val, MonoidHom.id_apply,
    AlgHom.mapDomain_id (A := DualNumber (Bialgebra.CounitAlgebra R A B)),
    MonoidHom.id_apply]

/-- The differential of a composite is the composite of the differentials. -/
@[simp]
lemma tangentKerMap_comp {A'' : Type*} [CommSemiring A''] [HopfAlgebra R A'']
    (φ : A' →ₐc[R] A) (χ : A'' →ₐc[R] A') :
    tangentKerMap (B := B) (φ.comp χ) =
      (tangentKerMap (B := B) χ).comp (tangentKerMap (B := B) φ) := by
  refine MonoidHom.ext fun ψ => Subtype.ext ?_
  rw [MonoidHom.comp_apply, tangentKerMap_apply_val, tangentKerMap_apply_val,
    tangentKerMap_apply_val,
    AlgHom.mapDomain_comp (A := DualNumber (Bialgebra.CounitAlgebra R A'' B)) φ χ]
  exact MonoidHom.comp_apply _ _ _

end Differential

end TauCeti
