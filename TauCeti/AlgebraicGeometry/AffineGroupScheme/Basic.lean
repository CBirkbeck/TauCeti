/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The category of affine group schemes over `Spec S`

This file introduces the category of affine group schemes over `Spec S` for a
commutative ring `S` — the full subcategory of group objects in schemes over `Spec S`
whose underlying scheme is affine — together with the two endpoint statements of the
reductive-groups roadmap's Layer 0 dictionary, stated for a plain-typed base ring `R`
and an arbitrary structure morphism rather than through `Scheme.Over` instance data:

* a commutative `R`-Hopf algebra structure on the global sections of an affine group
  scheme `φ : G ⟶ Spec R` (`hopfAlgebraGamma`);
* a group-object structure on `Spec A` over `Spec R` for a commutative `R`-Hopf
  algebra `A` (`grpObjSpec`).

Both consume the instances of Mathlib's `AlgebraicGeometry/Group/Affine.lean`.
Affineness enters only as the object property cutting out the full subcategory;
further refinements stay predicates rather than being baked into the category. The
anti-equivalence with commutative `S`-Hopf algebras is in
`TauCeti/AlgebraicGeometry/AffineGroupScheme/Equivalence.lean`.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Scheme Opposite

universe u

/-- The object property on group objects in schemes over `Spec S` selecting those whose
underlying scheme is affine. Over the affine base `Spec S` this is equivalent to the
structure morphism being an affine morphism; over a general base scheme only the
relative notion is correct, so this property must not be transplanted verbatim there. -/
@[expose] def affineGroupSchemeProperty (S : CommRingCat.{u}) :
    ObjectProperty (Grp (Over (Spec S))) :=
  fun G => IsAffine G.X.left

/-- Membership in the affine-group-scheme object property. -/
@[simp]
lemma affineGroupSchemeProperty_iff {S : CommRingCat.{u}} (G : Grp (Over (Spec S))) :
    affineGroupSchemeProperty S G ↔ IsAffine G.X.left :=
  Iff.rfl

/-- The category of affine group schemes over `Spec S`: the full subcategory of group
objects in schemes over `Spec S` whose underlying scheme is affine. -/
abbrev AffineGroupSchemeCat (S : CommRingCat.{u}) :=
  (affineGroupSchemeProperty S).FullSubcategory

instance (S : CommRingCat.{u}) : (affineGroupSchemeProperty S).IsClosedUnderIsomorphisms where
  of_iso e hG :=
    (IsAffine.iff_of_isIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom).mp hG

instance {S : CommRingCat.{u}} (G : AffineGroupSchemeCat S) : IsAffine G.obj.X.left :=
  G.property

variable {R : Type u} [CommRing R]

/-- Mathlib's Hopf-algebra structure on the global sections of an affine group scheme,
restated over a bundled ring `S : CommRingCat` with the arguments explicit. Not
redundant: the carrier `↥(CommRingCat.of R)` reduces to `R` before instance synthesis,
after which unification cannot match the bundled instance head, so a plain-typed goal
such as `HopfAlgebra R (Γ.obj (op G))` cannot find the instance directly; only an
explicitly applied bundled-`S` form survives, with definitional unfolding closing the
gap on application. `hopfAlgebraGamma` applies this form at `CommRingCat.of R`;
inlining it there fails to elaborate. -/
@[expose, instance_reducible] noncomputable def hopfAlgebraGammaOfOver
    (S : CommRingCat.{u}) (G : Scheme.{u})
    [G.Over (Spec S)] [GrpObj (G.asOver (Spec S))] [IsAffine G] :
    HopfAlgebra S (Γ.obj (op G)) :=
  inferInstanceAs (HopfAlgebra S Γ(G, ⊤))

/-- The global sections of an affine group scheme `φ : G ⟶ Spec R` are a commutative
`R`-Hopf algebra. This is the `Γ`-direction endpoint of the Layer 0 dictionary, stated
for an arbitrary structure morphism `φ` with the group structure carried by the object
`Over.mk φ` of schemes over `Spec R`. Not an instance, because `φ` is data that
instance search cannot recover from the goal. -/
@[expose, instance_reducible] noncomputable def hopfAlgebraGamma {G : Scheme.{u}}
    (φ : G ⟶ Spec (CommRingCat.of R)) [GrpObj (Over.mk φ)] [IsAffine G] :
    HopfAlgebra R (Γ.obj (op G)) :=
  letI : G.Over (Spec (CommRingCat.of R)) := ⟨φ⟩
  letI : GrpObj (G.asOver (Spec (CommRingCat.of R))) := ‹GrpObj (Over.mk φ)›
  hopfAlgebraGammaOfOver (CommRingCat.of R) G

/-- `Spec A` is a group object in schemes over `Spec R`, for a commutative `R`-Hopf
algebra `A`, with structure morphism `Spec (algebraMap R A)`. This is the
`Spec`-direction endpoint of the Layer 0 dictionary, stated on the explicit object
`Over.mk (Spec.map (algebraMap R A))`. -/
@[expose, instance_reducible] noncomputable def grpObjSpec (A : Type u) [CommRing A]
    [HopfAlgebra R A] : GrpObj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)) :
      Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))) :=
  inferInstanceAs (GrpObj ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))))

end TauCeti
