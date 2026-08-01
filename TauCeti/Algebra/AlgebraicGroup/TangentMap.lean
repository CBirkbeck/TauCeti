/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.Tangent

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
  -- Rewrite only the right-hand side into the `A`-side spelling; the left-hand sides
  -- agree definitionally since `mapDomain` acts by precomposition and the two counit
  -- coefficient algebras share the carrier `B`.
  rw [Bialgebra.CounitAlgebra.algebraMap_apply,
    ← CoalgHomClass.counit_comp_apply (F := A' →ₐc[R] A) φ a,
    ← Bialgebra.CounitAlgebra.algebraMap_apply (R := R) (A := A) (B := B)]
  exact h

/-- The differential of a Hopf-algebra morphism on tangent kernels: a morphism
`φ : A' →ₐc[R] A` of Hopf algebras sends a dual-number point of `A` over the identity to
a dual-number point of `A'` over the identity by precomposition. The coefficient
identification `Bialgebra.CounitAlgebra R A B = B = Bialgebra.CounitAlgebra R A' B` is
definitional, and the identity points correspond because `φ` intertwines the counits. -/
noncomputable def tangentKerMap (φ : A' →ₐc[R] A) :
    tangentKer R A B →* tangentKer R A' B where
  toFun ψ :=
    ⟨AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ ψ.val, by
      rw [mem_tangentKer_iff]
      ext a
      rw [AlgHom.comp_apply]
      exact fst_mapDomain_of_mem_tangentKer φ ψ.2 a⟩
  map_one' := Subtype.ext (map_one (AlgHom.mapDomain φ))
  map_mul' ψ χ := Subtype.ext (map_mul (AlgHom.mapDomain φ) ψ.val χ.val)

/-- The differential acts by precomposition on dual-number points. -/
@[simp]
lemma tangentKerMap_apply_val (φ : A' →ₐc[R] A) (ψ : tangentKer R A B) :
    (tangentKerMap φ ψ).val =
      AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ ψ.val := by
  -- `tangentKerMap` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ ψ.val = _
  rfl

/-- The differential of the identity morphism is the identity. -/
@[simp]
lemma tangentKerMap_id (ψ : tangentKer R A B) :
    tangentKerMap (BialgHom.id R A) ψ = ψ := by
  refine Subtype.ext ?_
  rw [tangentKerMap_apply_val]
  exact ofConv_injective (AlgHom.ext fun a => rfl)

/-- The differential of a composite is the composite of the differentials. -/
@[simp]
lemma tangentKerMap_comp {A'' : Type*} [CommSemiring A''] [HopfAlgebra R A'']
    (φ : A' →ₐc[R] A) (χ : A'' →ₐc[R] A') (ψ : tangentKer R A B) :
    tangentKerMap (B := B) (φ.comp χ) ψ = tangentKerMap χ (tangentKerMap φ ψ) := by
  refine Subtype.ext ?_
  rw [tangentKerMap_apply_val, tangentKerMap_apply_val, tangentKerMap_apply_val]
  exact ofConv_injective (AlgHom.ext fun a => rfl)

end Differential

end TauCeti
