/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.DimensionShift

/-!
# The augmentation ideal and the augmentation sequence

For a finite group `G` and a commutative ring `k`, the **augmentation** `k[G] ⟶ k` sends a group
ring element to the sum of its coefficients, and its kernel `I_G` is the **augmentation ideal**,
here taken as a representation of `G`. The **augmentation sequence** `0 ⟶ I_G ⟶ k[G] ⟶ k ⟶ 0`
is short exact, and because the left regular representation `k[G]` has vanishing Tate cohomology
for every subgroup, its connecting homomorphisms are isomorphisms
`Ĥⁿ(S, k) ≅ Ĥⁿ⁺¹(S, I_G)` in every degree and for every subgroup `S ≤ G`. This is the first of
the two dimension shifts behind Tate's theorem; the second is the splitting module of a
two-dimensional class.

## Main definitions

* `Rep.augmentation`: the augmentation `k[G] ⟶ k`.
* `Rep.augmentationIdeal`: the augmentation ideal `I_G`, the kernel of the augmentation.
* `Rep.augmentationSES`: the short exact sequence `I_G ⟶ k[G] ⟶ k`.

## Main statements

* `Rep.augmentationSES_shortExact`, `Rep.augmentationSES_res_shortExact`: the augmentation
  sequence is short exact, also after restriction to a subgroup.
* `TauCeti.TateCohomology.augmentationδIso`: `Ĥⁿ(S, k) ≅ Ĥⁿ⁺¹(S, I_G)` for every subgroup `S`
  of a finite group and every `n : ℤ`.
* `groupCohomology.isZero_H2_augmentationIdeal_res`: `H²(S, I_G) = 0` when `k` has no additive
  torsion, since it is `H¹(S, k) = Hom(S, k)`.

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

/-- The augmentation sends `r • g` to `r`. -/
@[simp]
theorem augmentation_hom_single (g : G) (r : k) :
    (augmentation k G).hom (MonoidAlgebra.single g r) = r := by
  simp

/-- The augmentation is surjective. -/
instance augmentation_epi : Epi (augmentation k G) :=
  (epi_iff_surjective _).2 fun r ↦ ⟨MonoidAlgebra.single 1 r, by simp⟩

/-- The **augmentation ideal** `I_G`, the kernel of the augmentation `k[G] ⟶ k`, as a
representation of `G`. -/
@[expose] def augmentationIdeal : Rep k G := kernel (augmentation k G)

/-- The inclusion of the augmentation ideal into the left regular representation. -/
@[expose] def augmentationι : augmentationIdeal k G ⟶ leftRegular k G := kernel.ι (augmentation k G)

/-- The inclusion of the augmentation ideal is a monomorphism. -/
instance augmentationι_mono : Mono (augmentationι k G) :=
  inferInstanceAs (Mono (kernel.ι (augmentation k G)))

/-- The **augmentation sequence** `I_G ⟶ k[G] ⟶ k`. -/
@[expose, implicit_reducible] def augmentationSES : ShortComplex (Rep k G) :=
  .mk (augmentationι k G) (augmentation k G) (kernel.condition (augmentation k G))

/-- The first term of the augmentation sequence is the augmentation ideal. -/
@[simp]
theorem augmentationSES_X₁ : (augmentationSES k G).X₁ = augmentationIdeal k G := rfl

/-- The middle term of the augmentation sequence is the left regular representation. -/
@[simp]
theorem augmentationSES_X₂ : (augmentationSES k G).X₂ = leftRegular k G := rfl

/-- The last term of the augmentation sequence is the trivial representation on `k`. -/
@[simp]
theorem augmentationSES_X₃ : (augmentationSES k G).X₃ = trivial k G k := rfl

/-- The augmentation sequence is short exact. -/
theorem augmentationSES_shortExact : (augmentationSES k G).ShortExact where
  exact := ShortComplex.exact_kernel (augmentation k G)
  mono_f := inferInstanceAs (Mono (augmentationι k G))
  epi_g := inferInstanceAs (Epi (augmentation k G))

/-- The augmentation sequence stays short exact after restriction along any group homomorphism
`f : H →* G`. -/
theorem augmentationSES_res_shortExact {H : Type u} [Group H] (f : H →* G) :
    ((augmentationSES k G).map (resFunctor f)).ShortExact :=
  (shortExact_res f).2 (augmentationSES_shortExact k G)

end Rep

namespace TauCeti.TateCohomology

open Rep

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype S]

variable (k) in
/-- The connecting homomorphism of the restricted augmentation sequence is an isomorphism in
every Tate degree, because the restriction of `k[G]` to `S` is Tate-acyclic. -/
theorem isIso_δ_augmentationSES_res (n : ℤ) :
    IsIso (_root_.TateCohomology.δ (augmentationSES_res_shortExact k G S.subtype) n) :=
  isIso_δ_of_isZero _ n (isZero_res_leftRegular S n) (isZero_res_leftRegular S (n + 1))

variable (k) in
/-- **The augmentation dimension shift**: `Ĥⁿ(S, k) ≅ Ĥⁿ⁺¹(S, I_G)` for every subgroup `S` of the
finite group `G` and every `n : ℤ`, given by the connecting homomorphism of the augmentation
sequence. -/
def augmentationδIso (n : ℤ) :
    tateCohomology (res S.subtype (trivial k G k)) n ≅
      tateCohomology (res S.subtype (augmentationIdeal k G)) (n + 1) :=
  haveI := isIso_δ_augmentationSES_res k S n
  asIso (_root_.TateCohomology.δ (augmentationSES_res_shortExact k G S.subtype) n)

/-- The augmentation dimension shift is the connecting homomorphism. -/
@[simp]
theorem augmentationδIso_hom (n : ℤ) :
    (augmentationδIso k S n).hom =
      _root_.TateCohomology.δ (augmentationSES_res_shortExact k G S.subtype) n := by
  rfl

end TauCeti.TateCohomology

namespace groupCohomology

open Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- Restriction to a subgroup of a trivial representation is a trivial representation. -/
instance isTrivial_res_trivial (S : Subgroup G) (V : Type u) [AddCommGroup V] [Module k V] :
    (res S.subtype (trivial k G V)).IsTrivial where
  out _ := rfl

/-- For a finite group `S` and a coefficient module `V` without additive torsion, every additive
homomorphism `S →+ V` vanishes: `|S| • f s = f (s ^ |S|) = f 1 = 0`. -/
theorem subsingleton_addMonoidHom_of_finite (S : Type u) [Group S] [Finite S] (V : Type u)
    [AddCommGroup V] [IsAddTorsionFree V] : Subsingleton (Additive S →+ V) := by
  refine subsingleton_of_forall_eq 0 fun f ↦ AddMonoidHom.ext fun s ↦ ?_
  have hs : Nat.card S • s = 0 := by
    rw [← ofMul_toMul s, ← ofMul_pow, pow_card_eq_one', ofMul_one]
  have h : Nat.card S • f s = 0 := by rw [← map_nsmul, hs, map_zero]
  rw [AddMonoidHom.zero_apply]
  exact (smul_eq_zero_iff_right Nat.card_pos.ne').1 h

/-- **`H¹(S, k) = 0` for a finite group `S` and a torsion-free coefficient ring `k`:** the
cohomology group is `Hom(S, k)`, which vanishes because `S` is finite and `k` is torsion-free. -/
theorem isZero_H1_res_trivial [Finite G] (S : Subgroup G) [IsAddTorsionFree k] :
    IsZero (groupCohomology (res S.subtype (trivial k G k)) 1) := by
  have : IsAddTorsionFree (res S.subtype (trivial k G k) : Type u) :=
    inferInstanceAs (IsAddTorsionFree k)
  have := subsingleton_addMonoidHom_of_finite S (res S.subtype (trivial k G k) : Type u)
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of k (Additive S →+ (res S.subtype (trivial k G k) : Type u)))).of_iso
    (H1IsoOfIsTrivial (res S.subtype (trivial k G k)))

/-- **`H²(S, I_G) = 0` for a torsion-free coefficient ring:** the connecting homomorphism of the
augmentation sequence identifies `H²(S, I_G)` with `H¹(S, k)`, which vanishes (Milne II, proof
of Theorem 3.11). -/
theorem isZero_H2_augmentationIdeal_res [Finite G] (S : Subgroup G) [IsAddTorsionFree k] :
    IsZero (groupCohomology (res S.subtype (augmentationIdeal k G)) 2) :=
  have : Fintype S := Fintype.ofFinite S
  (isZero_H1_res_trivial S).of_iso <|
    ((_root_.TateCohomology.isoGroupCohomology 2).app (res S.subtype (augmentationIdeal k G))).symm
      ≪≫ (TauCeti.TateCohomology.augmentationδIso k S 1).symm ≪≫
      (_root_.TateCohomology.isoGroupCohomology 1).app (res S.subtype (trivial k G k))

end groupCohomology
