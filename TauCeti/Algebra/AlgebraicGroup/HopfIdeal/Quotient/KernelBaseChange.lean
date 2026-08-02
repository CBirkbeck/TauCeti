/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel

/-!
# The kernel coordinate ring as a base change

The coordinate ring of the kernel of an affine group-scheme morphism is the quotient by
the kernel Hopf ideal `K·f(H⁺)`. This file identifies it with the base change
`K ⊗[H] R`, where `K` is an `H`-algebra through `f` and `R` an `H`-algebra through the
counit: this is Milne's description of the kernel as the fiber of `Spec K → Spec H` over
the identity point, `O(ker) = O(G) ⊗_{O(G')} R`, over an arbitrary commutative base ring
and with no flatness hypotheses.

The identification is assembled from Mathlib's
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot` (right exactness of the tensor
product) and the first isomorphism theorem for the counit
(`Ideal.quotientKerAlgEquivOfSurjective`); the two canonical algebra structures are
introduced with `letI` in the statement, as they are determined by `f` and the counit
rather than by instance search.

## Main declarations

* `TauCeti.CommHopfAlgCat.quotientKernelHopfIdealAlgEquiv`: the `K`-algebra equivalence
  from the kernel coordinate ring to `K ⊗[H] R`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{u} R}

/-- The coordinate ring of the kernel of an affine group-scheme morphism is the base
change of the identity point: `K ⧸ K·f(H⁺) ≃ₐ[K] K ⊗[H] R`, with `K` an `H`-algebra
through `f` and `R` an `H`-algebra through the counit. -/
noncomputable def quotientKernelHopfIdealAlgEquiv (f : H ⟶ K) :
    letI : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
    letI : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
    (↥K ⧸ (kernelHopfIdeal f).toIdeal) ≃ₐ[↥K] TensorProduct ↥H ↥K R := by
  letI : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
  letI : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
  refine AlgEquiv.trans (AlgEquiv.trans ?_
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot ↥K
      (HopfIdeal.augmentation R ↥H).toIdeal))
    (Algebra.TensorProduct.congr AlgEquiv.refl ?_)
  · -- The kernel Hopf ideal is the extension of the augmentation ideal along `f`,
    -- whose ring homomorphism is `algebraMap ↥H ↥K` for the `letI` structure.
    exact Ideal.quotientEquivAlgOfEq ↥K (by
      rw [kernelHopfIdeal_toIdeal]
      -- `algebraMap ↥H ↥K` for the `letI` structure is the ring homomorphism of
      -- `f.hom`; `rfl` performs that identification.
      rfl)
  · -- The counit quotient `H ⧸ H⁺ ≃ₐ[H] R`, by the first isomorphism theorem for the
    -- unique `H`-algebra map to `R`, whose kernel is the augmentation ideal.
    refine AlgEquiv.trans (Ideal.quotientEquivAlgOfEq ↥H ?_)
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId ↥H R) ?_)
    · rw [HopfIdeal.augmentation_toIdeal]
      -- `Algebra.ofId ↥H R` for the `letI` structure is the counit algebra map;
      -- `rfl` performs that identification.
      rfl
    · exact Bialgebra.counit_surjective

end CommHopfAlgCat

end TauCeti
