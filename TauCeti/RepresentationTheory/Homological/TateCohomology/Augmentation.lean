/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced
public import TauCeti.RepresentationTheory.Homological.TateCohomology.LongExactSequence

/-!
# The augmentation ideal and the augmentation sequence

For a finite group `G` and a commutative ring `k`, the **augmentation** `k[G] ⟶ k` sends a group
ring element to the sum of its coefficients, and its kernel `I_G` is the **augmentation ideal**,
here taken as a representation of `G`. The **augmentation sequence** `0 ⟶ I_G ⟶ k[G] ⟶ k ⟶ 0`
is short exact, and because the left regular representation `k[G]` has vanishing Tate cohomology
for every subgroup, its connecting homomorphisms are isomorphisms
`Ĥⁿ(S, k) ≅ Ĥⁿ⁺¹(S, I_G)` in every degree and for every subgroup `S ≤ G`. This is the first of
the two dimension shifts behind Tate's theorem; the second is the splitting module of a
two-dimensional class.

## Main definitions

* `Rep.augmentation`: the augmentation `k[G] ⟶ k`.
* `Rep.augmentationIdeal`: the augmentation ideal `I_G`, the kernel of the augmentation.
* `Rep.augmentationSES`: the short exact sequence `I_G ⟶ k[G] ⟶ k`.
* `Rep.augmentationιIsKernel`: the augmentation ideal is a kernel of the augmentation.

## Main statements

* `Rep.augmentationSES_shortExact`, `Rep.augmentationSES_res_shortExact`: the augmentation
  sequence is short exact, also after restriction to a subgroup.
* `TauCeti.TateCohomology.augmentationδIso`: `Ĥⁿ(S, k) ≅ Ĥⁿ⁺¹(S, I_G)` for every subgroup `S`
  of a finite group and every `n : ℤ`.
* `TauCeti.groupCohomology.isZero_H2_augmentationIdeal_res`: `H²(S, I_G) = 0` when `k` has no
  additive torsion, since it is `H¹(S, k) = Hom(S, k)`.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, proof of Theorem 3.11.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (3.1.4).
-/

public noncomputable section

universe u

open CategoryTheory Limits

namespace Rep

variable (k G : Type u) [CommRing k] [Group G]

/-- The **augmentation** `k[G] ⟶ k`, the map of representations sending a group ring element to
the sum of its coefficients; it is the map out of the left regular representation attached to
`1 : k`. -/
abbrev augmentation : leftRegular k G ⟶ trivial k G k := leftRegularHom (trivial k G k) 1

/-- The augmentation is surjective. -/
instance augmentation_epi : Epi (augmentation k G) :=
  (epi_iff_surjective _).2 fun r ↦ ⟨.single 1 r, by simp⟩

/-- The **augmentation ideal** `I_G`, the kernel of the augmentation `k[G] ⟶ k`, as a
representation of `G`, so that `Ĥⁿ(S, k) ≅ Ĥⁿ⁺¹(S, I_G)` for every subgroup `S` when `G` is
finite. -/
@[expose] def augmentationIdeal : Rep k G := kernel (augmentation k G)

/-- The inclusion of the augmentation ideal into the left regular representation. -/
def augmentationι : augmentationIdeal k G ⟶ leftRegular k G := kernel.ι (augmentation k G)

/-- The inclusion of the augmentation ideal is a monomorphism. -/
instance augmentationι_mono : Mono (augmentationι k G) :=
  inferInstanceAs (Mono (kernel.ι (augmentation k G)))

/-- The inclusion of the augmentation ideal followed by the augmentation is zero. -/
@[reassoc (attr := simp)]
theorem augmentationι_comp_augmentation : augmentationι k G ≫ augmentation k G = 0 :=
  kernel.condition (augmentation k G)

/-- The inclusion of the augmentation ideal is a kernel of the augmentation. -/
def augmentationιIsKernel :
    IsLimit (KernelFork.ofι (augmentationι k G) (augmentationι_comp_augmentation k G)) :=
  kernelIsKernel (augmentation k G)

/-- The **augmentation sequence** `I_G ⟶ k[G] ⟶ k`. -/
@[expose] def augmentationSES : ShortComplex (Rep k G) :=
  ShortComplex.kernelSequence (augmentation k G)

/-- The augmentation sequence has maps the inclusion of the augmentation ideal and the
augmentation. -/
theorem augmentationSES_def :
    augmentationSES k G = ShortComplex.mk (augmentationι k G) (augmentation k G)
      (augmentationι_comp_augmentation k G) :=
  (rfl)

/-- The first term of the augmentation sequence is the augmentation ideal. -/
@[simp]
theorem augmentationSES_X₁ : (augmentationSES k G).X₁ = augmentationIdeal k G := (rfl)

/-- The middle term of the augmentation sequence is the left regular representation. -/
@[simp]
theorem augmentationSES_X₂ : (augmentationSES k G).X₂ = leftRegular k G := (rfl)

/-- The last term of the augmentation sequence is the trivial representation on `k`. -/
@[simp]
theorem augmentationSES_X₃ : (augmentationSES k G).X₃ = trivial k G k := (rfl)

/-- The augmentation sequence is short exact. -/
theorem augmentationSES_shortExact : (augmentationSES k G).ShortExact where
  exact := ShortComplex.kernelSequence_exact (augmentation k G)
  mono_f := augmentationι_mono k G
  epi_g := augmentation_epi k G

/-- The augmentation sequence stays short exact after restriction along any monoid homomorphism
`f : H →* G`. -/
theorem augmentationSES_res_shortExact {H : Type*} [Monoid H] (f : H →* G) :
    ((augmentationSES k G).map (resFunctor f)).ShortExact :=
  (shortExact_res f).mpr (augmentationSES_shortExact k G)

variable {k G} in
/-- Restriction of a trivial representation along a monoid homomorphism is trivial. -/
instance {H : Type u} [Monoid H] (f : H →* G) (V : Type u) [AddCommGroup V] [Module k V] :
    (res f (trivial k G V)).IsTrivial where
  out _ := rfl

end Rep

namespace TauCeti.TateCohomology

open Rep

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype S]

variable (k) in
/-- **The augmentation dimension shift**: `Ĥⁿ(S, k) ≅ Ĥⁿ⁺¹(S, I_G)` for every subgroup `S` of the
finite group `G` and every `n : ℤ`, given by the connecting homomorphism of the augmentation
sequence. -/
def augmentationδIso (n : ℤ) :
    tateCohomology (res S.subtype (trivial k G k)) n ≅
      tateCohomology (res S.subtype (augmentationIdeal k G)) (n + 1) :=
  -- the restriction of `k[G]` to `S` is Tate-acyclic
  δIso (augmentationSES_res_shortExact k G S.subtype) n (isZero_res_leftRegular S n)
    (isZero_res_leftRegular S (n + 1))

/-- The augmentation dimension shift is the connecting homomorphism. -/
@[simp]
theorem augmentationδIso_hom (n : ℤ) :
    (augmentationδIso k S n).hom =
      _root_.TateCohomology.δ (augmentationSES_res_shortExact k G S.subtype) n :=
  δIso_hom _ n _ _

end TauCeti.TateCohomology

namespace TauCeti.groupCohomology

open _root_.groupCohomology Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- **`H²(S, I_G) = 0`** for a subgroup `S` of a finite group `G` and a coefficient ring `k`
without additive torsion. -/
theorem isZero_H2_augmentationIdeal_res [Finite G] (S : Subgroup G) [IsAddTorsionFree k] :
    IsZero (groupCohomology (res S.subtype (augmentationIdeal k G)) 2) :=
  -- the connecting homomorphism of the augmentation sequence identifies `H²(S, I_G)` with
  -- `H¹(S, k)`, which vanishes (Milne II, proof of Theorem 3.11)
  have : Fintype S := Fintype.ofFinite S
  (isZero_H1_of_isTrivial (res S.subtype (trivial k G k))).of_iso <|
    ((_root_.TateCohomology.isoGroupCohomology 2).app (res S.subtype (augmentationIdeal k G))).symm
      ≪≫ (TateCohomology.augmentationδIso k S 1).symm ≪≫
      (_root_.TateCohomology.isoGroupCohomology 1).app (res S.subtype (trivial k G k))

end TauCeti.groupCohomology
