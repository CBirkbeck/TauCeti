/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Basic

/-!
# Affine group schemes are anti-equivalent to commutative Hopf algebras

Over a commutative ring `S`, the contravariant functor `Spec` is an equivalence from the
opposite of the category of commutative `S`-Hopf algebras onto the category of affine
group schemes over `Spec S`. This is the assembled Layer 0 dictionary of the
reductive-groups roadmap.

Mathlib's `AlgebraicGeometry/Group/Affine.lean` provides the functor
(`AlgebraicGeometry.hopfSpec`), its full faithfulness, and the characterization of its
essential image as the affine group schemes (`AlgebraicGeometry.essImage_hopfSpec`);
this file composes them into the equivalence with the category
`TauCeti.AffineGroupSchemeCat` of the parent file.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- `Spec` as an anti-equivalence from commutative `S`-Hopf algebras onto affine group
schemes over `Spec S`. The underlying functor is Mathlib's `AlgebraicGeometry.hopfSpec`,
which is fully faithful with essential image the affine group schemes; the isomorphism
`commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso` records this on the level
of functors. -/
-- `@[expose]` is load-bearing, not a leak: the exported `rfl`-lemmas below unfold this
-- definition, and the module system rejects an exported `rfl`-proof whose unfolding
-- chain is not exposed ("all definitions that need to be unfolded ... must be exposed").
@[expose] noncomputable def commHopfAlgCatOpEquivAffineGroupSchemeCat (S : CommRingCat.{u}) :
    (CommHopfAlgCat S)ᵒᵖ ≌ AffineGroupSchemeCat S :=
  (hopfSpec S).toEssImage.asEquivalence.trans
    (ObjectProperty.fullSubcategoryCongr
      (funext fun G => propext (essImage_hopfSpec.trans (affineGroupSchemeProperty_iff G).symm)))

/-- The forward functor of `commHopfAlgCatOpEquivAffineGroupSchemeCat`, followed by the
inclusion of the full subcategory, is `hopfSpec`: the anti-equivalence really does act
by `Spec`. -/
noncomputable def commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
    (S : CommRingCat.{u}) :
    (commHopfAlgCatOpEquivAffineGroupSchemeCat S).functor ⋙
      (affineGroupSchemeProperty S).ι ≅ hopfSpec S :=
  (hopfSpec S).toEssImageCompι

/-- On objects, the anti-equivalence sends a commutative Hopf algebra to its `hopfSpec`
group scheme. -/
@[simp]
lemma commHopfAlgCatOpEquivAffineGroupSchemeCat_functor_obj_obj (S : CommRingCat.{u})
    (H : (CommHopfAlgCat S)ᵒᵖ) :
    ((commHopfAlgCatOpEquivAffineGroupSchemeCat S).functor.obj H).obj =
      (hopfSpec S).obj H :=
  rfl

/-- On morphisms, the anti-equivalence acts as `hopfSpec` does: the underlying morphism
of the image of `f` is `(hopfSpec S).map f`. -/
@[simp]
lemma commHopfAlgCatOpEquivAffineGroupSchemeCat_functor_map (S : CommRingCat.{u})
    {H K : (CommHopfAlgCat S)ᵒᵖ} (f : H ⟶ K) :
    ((commHopfAlgCatOpEquivAffineGroupSchemeCat S).functor.map f).hom =
      (hopfSpec S).map f :=
  rfl

end TauCeti
