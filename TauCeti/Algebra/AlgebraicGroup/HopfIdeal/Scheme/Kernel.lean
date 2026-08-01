/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map

/-!
# The kernel of a morphism of affine group schemes

A morphism `f : H ⟶ K` of commutative Hopf algebras induces contravariantly a morphism of
affine group schemes `Spec K ⟶ Spec H` over `Spec R`. Its kernel is the closed subgroup
scheme of `Spec K` cut out by the kernel Hopf ideal: the image under `f` of the
augmentation ideal of `H`, whose quotient coordinate ring is `K ⊗[H] R`.

This file constructs the kernel Hopf ideal, the kernel closed subgroup scheme, and its
closed immersion into the source, and proves the defining triangle: composing the induced
group-scheme morphism with the kernel inclusion is the trivial morphism, because the
composite coordinate map `H ⟶ K ⟶ K ⧸ K·f(H⁺)` is the counit-unit composite.

## Main declarations

* `TauCeti.CommHopfAlgCat.kernelHopfIdeal`: the kernel Hopf ideal of a morphism.
* `TauCeti.CommHopfAlgCat.mem_kernelHopfIdeal_of_mem_augmentation`: its generators.
* `TauCeti.CommHopfAlgCat.kernelSpec` and `TauCeti.CommHopfAlgCat.kernelSpecι`: the kernel
  closed subgroup scheme and its inclusion (a closed immersion, by
  `TauCeti.CommHopfAlgCat.isClosedImmersion_quotientSpecι`).
* `TauCeti.CommHopfAlgCat.comp_mkQuotient_kernelHopfIdeal`: the coordinate-ring triangle.
* `TauCeti.CommHopfAlgCat.kernelSpecι_comp`: the scheme-level triangle.

## References

Milne, *Algebraic Groups*, Proposition 4.1: the kernel of a homomorphism of affine
algebraic groups is represented by `O(K) / I_H O(K)` for `I_H` the augmentation ideal.
The same-universe restriction on the Hopf algebras is imposed by Mathlib's current
`hopfSpec` construction, as in `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace CommHopfAlgCat

open AlgebraicGeometry

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{u} R}

/-- The kernel Hopf ideal of a morphism of commutative Hopf algebras: the image of the
augmentation ideal of the source. Its quotient represents the kernel of the induced
morphism of affine group schemes. -/
noncomputable abbrev kernelHopfIdeal (f : H ⟶ K) : HopfIdeal R K :=
  (HopfIdeal.augmentation R H).map f.hom

/-- The kernel Hopf ideal contains the image of every counit-vanishing element. -/
theorem mem_kernelHopfIdeal_of_mem_augmentation (f : H ⟶ K) {x : H}
    (hx : Coalgebra.counit (R := R) x = 0) : f.hom x ∈ kernelHopfIdeal f :=
  HopfIdeal.mem_map_of_mem f.hom ((HopfIdeal.mem_augmentation R H).mpr hx)

/-- The kernel of the induced morphism of affine group schemes, as an affine group
scheme: the closed subgroup scheme of the source cut out by the kernel Hopf ideal. -/
noncomputable abbrev kernelSpec (f : H ⟶ K) :
    Grp (Over (Spec (CommRingCat.of R))) :=
  quotientSpec K (kernelHopfIdeal f)

/-- The inclusion of the kernel into the source group scheme. Its underlying scheme
morphism is a closed immersion by
`TauCeti.CommHopfAlgCat.isClosedImmersion_quotientSpecι`. -/
noncomputable abbrev kernelSpecι (f : H ⟶ K) :
    kernelSpec f ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K) :=
  quotientSpecι K (kernelHopfIdeal f)

-- Mathlib has no application lemma for `Bialgebra.unitBialgHom`; this contains its
-- definitional unfolding to `algebraMap` in one place (upstream candidate).
private lemma unitBialgHom_apply {A : Type u} [Semiring A] [Bialgebra R A] (r : R) :
    Bialgebra.unitBialgHom R A r = algebraMap R A r :=
  rfl

/-- The coordinate-ring triangle defining the kernel: composing `f` with the quotient by
the kernel Hopf ideal is the counit-unit composite, i.e. the coordinate map of the trivial
group-scheme morphism. -/
theorem comp_mkQuotient_kernelHopfIdeal (f : H ⟶ K) :
    f ≫ mkQuotient K (kernelHopfIdeal f) =
      _root_.CommHopfAlgCat.ofHom
        ((Bialgebra.unitBialgHom R (quotient K (kernelHopfIdeal f))).comp
          (Bialgebra.counitBialgHom R H)) := by
  ext h
  have hmem : f.hom h - algebraMap R K (Coalgebra.counit (R := R) h) ∈
      kernelHopfIdeal f := by
    have hx : Coalgebra.counit (R := R)
        (h - algebraMap R H (Coalgebra.counit (R := R) h)) = 0 := by
      simp
    simpa [map_sub, AlgHomClass.commutes] using
      mem_kernelHopfIdeal_of_mem_augmentation f hx
  have hquot :
      (mkQuotient K (kernelHopfIdeal f)).hom
          (f.hom h - algebraMap R K (Coalgebra.counit (R := R) h)) = 0 :=
    (mkQuotient_eq_zero_iff K (kernelHopfIdeal f) _).mpr
      (HopfIdeal.mem_toIdeal.mpr hmem)
  rw [map_sub, sub_eq_zero] at hquot
  simpa [unitBialgHom_apply] using hquot

/-- The scheme-level triangle: the composite of the kernel inclusion with the induced
group-scheme morphism is the trivial morphism, the image under `hopfSpec` of the
counit-unit composite. -/
theorem kernelSpecι_comp (f : H ⟶ K) :
    kernelSpecι f ≫ (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (_root_.CommHopfAlgCat.ofHom
          ((Bialgebra.unitBialgHom R (quotient K (kernelHopfIdeal f))).comp
            (Bialgebra.counitBialgHom R H))).op := by
  rw [kernelSpecι, quotientSpecι_def, ← Functor.map_comp, ← op_comp,
    comp_mkQuotient_kernelHopfIdeal]

end CommHopfAlgCat

end TauCeti
