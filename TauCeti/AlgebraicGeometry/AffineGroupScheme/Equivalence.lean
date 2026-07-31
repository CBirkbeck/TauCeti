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
which is fully faithful with essential image the affine group schemes. -/
noncomputable def commHopfAlgCatOpEquivAffineGroupSchemeCat (S : CommRingCat.{u}) :
    (CommHopfAlgCat S)ᵒᵖ ≌ AffineGroupSchemeCat S :=
  (hopfSpec S).toEssImage.asEquivalence.trans
    (ObjectProperty.fullSubcategoryCongr (funext fun _ => propext essImage_hopfSpec))

end TauCeti
