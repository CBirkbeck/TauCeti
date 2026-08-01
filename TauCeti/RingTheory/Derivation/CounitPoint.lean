/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
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

end TauCeti
