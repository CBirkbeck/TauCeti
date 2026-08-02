/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Map

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
-/

public section

namespace TauCeti

open Coalgebra

section DerivationMap

variable {R A A' B : Type*} [CommSemiring R]
  [CommSemiring A] [Bialgebra R A] [CommSemiring A'] [Bialgebra R A']
  [CommSemiring B] [Algebra R B]

/-- Precomposition of a counit-valued derivation with a bialgebra morphism: the additive
form of the differential.

The domain restriction is `Derivation.compAlgebraMap` over local scalar-tower instances
making `φ` the canonical algebra map, and the coefficients then move across the canonical
`A'`-linear identification of the two counit coefficient algebras, whose linearity is the
counit compatibility of `φ`. -/
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

end DerivationMap

end TauCeti
