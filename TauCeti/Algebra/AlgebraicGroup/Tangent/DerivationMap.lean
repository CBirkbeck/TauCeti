/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic

/-!
# The differential on derivations

A morphism `φ : A' →ₐc[R] A` of bialgebras sends a counit-valued derivation of `A` to
one of `A'` by precomposition. The construction splits the transport into the two halves
Mathlib provides: restricting the domain along `φ` (`Derivation.compAlgebraMap`, over
local scalar-tower instances for `φ`), and moving the coefficients across the canonical
identification of the two counit coefficient algebras, which is `A'`-linear precisely
because bialgebra morphisms intertwine counits (`LinearEquiv.compDer`). The Leibniz rule
therefore comes from those two facts and is not reproved here.

## Main declarations

* `TauCeti.derivationComp`: precomposition of counit-valued derivations along a
  bialgebra morphism.
* `TauCeti.derivationComp_apply`: it acts by precomposition.
The intertwining with the tangent dictionaries is
`TauCeti.tangentKerMap_derivationMulEquivTangentKer` in
`TauCeti.Algebra.AlgebraicGroup.Tangent.Map`.
-/

public section

namespace TauCeti

open Coalgebra

section DerivationMap

variable {R A A' B : Type*} [CommSemiring R]
  [CommSemiring A] [Bialgebra R A] [CommSemiring A'] [Bialgebra R A']
  [CommSemiring B] [Algebra R B]

/-- Precomposition of a counit-valued derivation with a bialgebra morphism: the map
sending an `R`-derivation `d : A → B` at the identity point of `A` to the derivation
`a ↦ d (φ a)` at the identity point of `A'` — the additive form of the differential.

(The commutativity hypotheses on `A` and `A'` are those of `Derivation` itself;
commutativity of `B` is used to install the restricted algebra structure via
`RingHom.toAlgebra`.) -/
noncomputable def derivationComp (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    Derivation R A' (Bialgebra.CounitAlgebra R A' B) := by
  letI : Algebra A' A := (φ : A' →ₐ[R] A).toAlgebra
  letI : IsScalarTower R A' A := IsScalarTower.of_algHom (φ : A' →ₐ[R] A)
  let ρ : A' →ₐ[R] Bialgebra.CounitAlgebra R A B :=
    (IsScalarTower.toAlgHom R A (Bialgebra.CounitAlgebra R A B)).comp (φ : A' →ₐ[R] A)
  letI : Algebra A' (Bialgebra.CounitAlgebra R A B) := ρ.toAlgebra
  letI : IsScalarTower R A' (Bialgebra.CounitAlgebra R A B) := IsScalarTower.of_algHom ρ
  letI : IsScalarTower A' A (Bialgebra.CounitAlgebra R A B) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let eRing : Bialgebra.CounitAlgebra R A B ≃+* Bialgebra.CounitAlgebra R A' B :=
    (Bialgebra.CounitAlgebra.algEquivSelf R A B).toRingEquiv.trans
      (Bialgebra.CounitAlgebra.algEquivSelf R A' B).symm.toRingEquiv
  let e : Bialgebra.CounitAlgebra R A B ≃ₐ[A'] Bialgebra.CounitAlgebra R A' B :=
    AlgEquiv.ofRingEquiv (f := eRing) (by
      intro a
      -- The single mathematical obligation: the two `A'`-algebra maps agree because
      -- `φ` intertwines the counits. The transports erase pointwise, the left algebra
      -- map is `algebraMap A (CounitAlgebra R A B)` at `φ a` by the local instance, and
      -- both sides then reduce through the counit.
      simp only [eRing, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
        Bialgebra.CounitAlgebra.algEquivSelf_apply]
      rw [show (algebraMap A' (Bialgebra.CounitAlgebra R A B)) a =
          algebraMap A (Bialgebra.CounitAlgebra R A B) ((φ : A' →ₐ[R] A) a) from rfl,
        Bialgebra.CounitAlgebra.algebraMap_apply R A B,
        Bialgebra.CounitAlgebra.algebraMap_apply R A' B,
        Bialgebra.CounitAlgebra.algEquivSelf_symm_apply R A' B]
      exact congrArg (algebraMap R B)
        (DFunLike.congr_fun (BialgHom.counitAlgHom_comp φ) a))
  exact e.toLinearEquiv.compDer (d.compAlgebraMap A')

/-- The differential acts on derivations by precomposition. -/
@[simp]
lemma derivationComp_apply (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A') :
    derivationComp (B := B) φ d a = d ((φ : A' →ₐ[R] A) a) := by
  simp only [derivationComp, Derivation.linearEquiv_coe_comp, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
    Bialgebra.CounitAlgebra.algEquivSelf_apply]
  -- The remaining transport erases at this value, and the precomposition is
  -- definitional in Mathlib's `compAlgebraMap`.
  exact (Bialgebra.CounitAlgebra.algEquivSelf_symm_apply R A' B _).trans rfl

/-- Precomposition of counit-valued derivations, bundled as an `R`-linear map. -/
noncomputable def derivationCompₗ (φ : A' →ₐc[R] A) :
    Derivation R A (Bialgebra.CounitAlgebra R A B) →ₗ[R]
      Derivation R A' (Bialgebra.CounitAlgebra R A' B) where
  toFun := derivationComp φ
  -- After simplification both sides are the same value of `B`; the residual is the
  -- definitional identification of the two coefficient indexings.
  map_add' d₁ d₂ := by ext a; simp; rfl
  map_smul' r d := by ext a; simp; rfl

@[simp]
lemma derivationCompₗ_apply (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    derivationCompₗ (B := B) φ d = derivationComp φ d := by
  -- `derivationCompₗ` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change derivationComp φ d = _
  rfl

/-- Precomposition along the identity is the identity. -/
@[simp]
theorem derivationComp_id (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    derivationComp (B := B) (BialgHom.id R A) d = d := by
  ext a
  simp

/-- Precomposition along a composite is the composite of the precompositions. -/
@[simp]
theorem derivationComp_comp {A'' : Type*} [CommSemiring A''] [Bialgebra R A'']
    (φ : A' →ₐc[R] A) (χ : A'' →ₐc[R] A')
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    derivationComp (B := B) (φ.comp χ) d = derivationComp χ (derivationComp φ d) := by
  ext a
  simp
  -- The residual is the definitional identification of the coefficient indexings.
  rfl

end DerivationMap

end TauCeti
