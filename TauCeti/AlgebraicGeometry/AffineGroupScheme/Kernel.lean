/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Basic

/-!
# Hopf ideals give closed immersions of affine group schemes

A Hopf ideal `I` of a commutative Hopf algebra `A` over `S` induces a morphism of
affine group schemes `Spec (A ⧸ I) ⟶ Spec A` over `Spec S`, and the underlying
morphism of schemes is a closed immersion: the scheme-side closed subgroup scheme cut
out by a Hopf ideal (reductive-groups roadmap, Layer 3). Group-theoretic kernel
properties of this inclusion are follow-up work; this file provides the morphism and
its closed-immersion property.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry HopfAlgebra Opposite

universe u

variable (S : CommRingCat.{u}) (A : Type u) [CommRing A] [HopfAlgebra S A]
  (I : Ideal A) [I.IsTwoSided] [I.IsHopfIdeal S]

/-- The morphism of affine group schemes over `Spec S` induced by a Hopf ideal
`I ⊆ A`: the `Spec` of the quotient map `A →ₐc[S] A ⧸ I`. -/
noncomputable def hopfIdealSpecMap :
    (hopfSpec S).obj (op (CommHopfAlgCat.of S (A ⧸ I))) ⟶
      (hopfSpec S).obj (op (CommHopfAlgCat.of S A)) :=
  (hopfSpec S).map (CommHopfAlgCat.ofHom (Bialgebra.Quotient.mkBialgHom I)).op

/-- The underlying scheme morphism of `hopfIdealSpecMap` is `Spec` of the quotient map. -/
theorem hopfIdealSpecMap_hom_hom_left :
    (hopfIdealSpecMap S A I).hom.hom.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rfl

/-- The underlying scheme morphism of `hopfIdealSpecMap` is a closed immersion:
a Hopf ideal cuts out a closed subgroup scheme. -/
theorem isClosedImmersion_hopfIdealSpecMap :
    IsClosedImmersion (hopfIdealSpecMap S A I).hom.hom.left := by
  rw [hopfIdealSpecMap_hom_hom_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

end TauCeti
