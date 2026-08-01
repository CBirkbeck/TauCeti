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
augmentation ideal of `H` — the ideal `K·f(H⁺)` of the coordinate ring of the *source*
group scheme, which the classical theory identifies with the defining ideal of
`Spec (K ⊗[H] R)` (that base-change identification is not formalized here).

This file constructs the kernel Hopf ideal, the kernel closed subgroup scheme, and its
closed immersion into the source, and proves the trivialization criterion that gives the
construction its kernel semantics among Hopf-ideal quotients: a morphism out of `K` kills
the kernel Hopf ideal *exactly* when its composite with `f` is the trivial (counit-unit)
morphism. In particular the composite of the induced group-scheme morphism with the kernel
inclusion is trivial, and any quotient closed subgroup scheme `quotientSpec K J` on which
`f` trivializes satisfies `kernelHopfIdeal f ≤ J`, hence includes into the kernel via
`TauCeti.CommHopfAlgCat.quotientSpecMapOfLe`, compatibly with the inclusions
(`TauCeti.CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι`); the coordinate-level
factorization and its uniqueness are `TauCeti.CommHopfAlgCat.liftQuotient` and
`TauCeti.CommHopfAlgCat.liftQuotient_unique`. The pullback square against the unit
section is future work.

## Main declarations

* `TauCeti.CommHopfAlgCat.kernelHopfIdeal`: the kernel Hopf ideal of a morphism.
* `TauCeti.CommHopfAlgCat.mem_kernelHopfIdeal_of_mem_augmentation`: its generators.
* `TauCeti.CommHopfAlgCat.kernelSpec` and `TauCeti.CommHopfAlgCat.kernelSpecι`: the kernel
  closed subgroup scheme and its inclusion (a closed immersion, by
  `TauCeti.CommHopfAlgCat.isClosedImmersion_quotientSpecι`).
* `TauCeti.CommHopfAlgCat.kernelHopfIdeal_toIdeal_le_ker_iff` and
  `TauCeti.CommHopfAlgCat.comp_eq_unit_comp_counit_iff`: the trivialization criterion — a
  map out of the coordinate ring kills the kernel Hopf ideal exactly when its composite
  with `f` is trivial.
* `TauCeti.CommHopfAlgCat.kernelHopfIdeal_le_iff`: its Hopf-ideal-quotient form.
* `TauCeti.CommHopfAlgCat.comp_mkQuotient_kernelHopfIdeal`: the coordinate-ring triangle.
* `TauCeti.CommHopfAlgCat.kernelSpecι_comp`: the scheme-level triangle.

## References

Milne, *Algebraic Groups*, Proposition 4.1: the kernel of a homomorphism of affine
algebraic groups is represented by `O(K) / I_H O(K)` for `I_H` the augmentation ideal.
The same-universe restriction on the Hopf algebras is imposed by Mathlib's current
`hopfSpec` construction, as in `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u w

namespace CommHopfAlgCat

open AlgebraicGeometry

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{u} R}

/-- The kernel Hopf ideal of a morphism of commutative Hopf algebras: the image of the
augmentation ideal of the source. It is an ideal of the *codomain* `K`, the coordinate
ring of the source of the induced group-scheme morphism `Spec K ⟶ Spec H`; its quotient
represents the kernel of that morphism. -/
noncomputable def kernelHopfIdeal (f : H ⟶ K) : HopfIdeal R K :=
  (HopfIdeal.augmentation R H).map f.hom

/-- The underlying ideal of the kernel Hopf ideal is the extension of the augmentation
ideal. -/
@[simp]
theorem kernelHopfIdeal_toIdeal (f : H ⟶ K) :
    (kernelHopfIdeal f).toIdeal =
      Ideal.map (f.hom : ↥H →+* ↥K) (HopfIdeal.augmentation R H).toIdeal := by
  -- `kernelHopfIdeal` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding to a `HopfIdeal.map` application.
  change ((HopfIdeal.augmentation R H).map f.hom).toIdeal = _
  rw [HopfIdeal.map_toIdeal]

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
noncomputable def kernelSpecι (f : H ⟶ K) :
    kernelSpec f ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K) :=
  quotientSpecι K (kernelHopfIdeal f)

/-- `kernelSpecι` is the quotient inclusion at the kernel Hopf ideal. -/
theorem kernelSpecι_def (f : H ⟶ K) :
    kernelSpecι f = quotientSpecι K (kernelHopfIdeal f) := by
  -- `kernelSpecι` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change quotientSpecι K (kernelHopfIdeal f) = _
  rfl

-- Mathlib has no application lemma for `Bialgebra.unitBialgHom`; this contains its
-- definitional unfolding to `algebraMap` in one place (upstream candidate).
private lemma unitBialgHom_apply {A : Type u} [Semiring A] [Bialgebra R A] (r : R) :
    Bialgebra.unitBialgHom R A r = algebraMap R A r :=
  rfl

/-- The difference between a morphism value and the counit-unit value lies in the kernel
Hopf ideal. -/
private theorem sub_algebraMap_counit_mem_kernelHopfIdeal (f : H ⟶ K) (h : H) :
    f.hom h - algebraMap R K (Coalgebra.counit (R := R) h) ∈ kernelHopfIdeal f := by
  have hx : Coalgebra.counit (R := R)
      (h - algebraMap R H (Coalgebra.counit (R := R) h)) = 0 := by
    simp
  simpa [map_sub, AlgHomClass.commutes] using
    mem_kernelHopfIdeal_of_mem_augmentation f hx

/-- Algebra-level trivialization criterion: an algebra map out of the coordinate ring of
the source group scheme kills the kernel Hopf ideal exactly when its composite with `f`
is the counit-unit composite. This is the kernel property tested against an arbitrary
commutative `R`-algebra; `TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff` (in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel`) packages it on the functors of
points. -/
theorem kernelHopfIdeal_toIdeal_le_ker_iff (f : H ⟶ K) {A : Type w} [Ring A]
    [Algebra R A] (φ : ↥K →ₐ[R] A) :
    (kernelHopfIdeal f).toIdeal ≤ RingHom.ker φ.toRingHom ↔
      φ.comp (f.hom : ↥H →ₐ[R] ↥K) =
        (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R ↥H) := by
  constructor
  · intro hle
    ext h
    have hker := hle (HopfIdeal.mem_toIdeal.mpr (sub_algebraMap_counit_mem_kernelHopfIdeal f h))
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
    simpa [Algebra.ofId_apply, AlgHomClass.commutes] using hker
  · intro heq
    rw [kernelHopfIdeal_toIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    have hx0 : Coalgebra.counit (R := R) x = 0 :=
      (HopfIdeal.mem_augmentation R H).mp (HopfIdeal.mem_toIdeal.mp hx)
    have hval := congrArg (fun ψ : ↥H →ₐ[R] A => ψ x) heq
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply] at hval
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa [hx0] using hval

/-- The trivialization criterion for Hopf-algebra morphisms: a morphism out of `K` kills
the kernel Hopf ideal of `f` exactly when its composite with `f` is the trivial
(counit-unit) morphism. -/
theorem comp_eq_unit_comp_counit_iff (f : H ⟶ K) {L : _root_.CommHopfAlgCat.{u} R}
    (g : K ⟶ L) :
    f ≫ g =
        _root_.CommHopfAlgCat.ofHom
          ((Bialgebra.unitBialgHom R L).comp (Bialgebra.counitBialgHom R H)) ↔
      (kernelHopfIdeal f).toIdeal ≤ RingHom.ker g.hom.toAlgHom.toRingHom := by
  rw [kernelHopfIdeal_toIdeal_le_ker_iff f g.hom.toAlgHom]
  constructor
  · intro heq
    ext h
    have hval := congrArg (fun ψ : H ⟶ L => ψ.hom h) heq
    simpa [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.hom_ofHom,
      BialgHom.comp_apply, unitBialgHom_apply, Algebra.ofId_apply] using hval
  · intro heq
    ext h
    have hval := congrArg (fun ψ : ↥H →ₐ[R] ↥L => ψ h) heq
    simpa [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.hom_ofHom,
      BialgHom.comp_apply, unitBialgHom_apply, Algebra.ofId_apply] using hval

/-- The coordinate-ring triangle: composing `f` with the quotient by its kernel Hopf
ideal is the counit-unit composite, i.e. the coordinate map of the trivial group-scheme
morphism. -/
@[simp]
theorem comp_mkQuotient_kernelHopfIdeal (f : H ⟶ K) :
    f ≫ mkQuotient K (kernelHopfIdeal f) =
      _root_.CommHopfAlgCat.ofHom
        ((Bialgebra.unitBialgHom R (quotient K (kernelHopfIdeal f))).comp
          (Bialgebra.counitBialgHom R H)) :=
  (comp_eq_unit_comp_counit_iff f _).mpr (mkQuotient_ker K (kernelHopfIdeal f) ▸ le_rfl)

/-- The Hopf-ideal-quotient form of the trivialization criterion: `f` trivializes on the
closed subgroup scheme cut out by `J` exactly when `J` contains the kernel Hopf ideal.
Combined with `TauCeti.CommHopfAlgCat.quotientSpecMapOfLe` and
`TauCeti.CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι`, such a quotient closed
subgroup scheme includes into the kernel compatibly with the inclusions. -/
theorem kernelHopfIdeal_le_iff (f : H ⟶ K) {J : HopfIdeal R K} :
    kernelHopfIdeal f ≤ J ↔
      f ≫ mkQuotient K J =
        _root_.CommHopfAlgCat.ofHom
          ((Bialgebra.unitBialgHom R (quotient K J)).comp
            (Bialgebra.counitBialgHom R H)) := by
  rw [comp_eq_unit_comp_counit_iff, mkQuotient_ker]
  exact HopfIdeal.toIdeal_le_toIdeal.symm

/-- The scheme-level triangle: the composite of the kernel inclusion with the induced
group-scheme morphism is the trivial morphism, the image under `hopfSpec` of the
counit-unit composite. -/
@[simp]
theorem kernelSpecι_comp (f : H ⟶ K) :
    kernelSpecι f ≫ (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (_root_.CommHopfAlgCat.ofHom
          ((Bialgebra.unitBialgHom R (quotient K (kernelHopfIdeal f))).comp
            (Bialgebra.counitBialgHom R H))).op := by
  rw [kernelSpecι_def, quotientSpecι_def, ← Functor.map_comp, ← op_comp,
    comp_mkQuotient_kernelHopfIdeal]

end CommHopfAlgCat

end TauCeti
