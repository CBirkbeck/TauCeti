/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced

/-!
# Dimension shifting

For a representation `A` of a group `G`, the embedding `A ⟶ Coind_⊥^G A` into the coinduced
module and the projection `Ind_⊥^G A ⟶ A` from the induced module give short exact sequences

`0 ⟶ A ⟶ Coind_⊥^G A ⟶ up A ⟶ 0` and `0 ⟶ down A ⟶ Ind_⊥^G A ⟶ A ⟶ 0`.

Since the middle terms have vanishing positive-degree cohomology (resp. homology), and, for a
finite group, vanishing Tate cohomology in every degree, the connecting homomorphisms of the long
exact sequences identify `Hⁿ⁺¹(G, up A) ≅ Hⁿ⁺²(G, A)`, `Ĥⁿ(G, up A) ≅ Ĥⁿ⁺¹(G, A)` and
`Ĥⁿ(G, A) ≅ Ĥⁿ⁺¹(G, down A)`, and likewise after restriction to any subgroup. This is the
*dimension shifting* of Milne, *Class Field Theory*, II 1.13 and 1.28.

The file also records the compatibility of the connecting homomorphism of ordinary cohomology
with restriction along a group homomorphism, which is needed to compare maps defined by
dimension shifting.

The constructions follow `ClassFieldTheory/Cohomology/Functors/UpDown.lean` and
`Functors/Restriction.lean` in `kbuzzard/ClassFieldTheory`, commit
`ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main definitions

* `Rep.up`, `Rep.upSES`: the cokernel of `A ⟶ Coind_⊥^G A` and its short exact sequence.
* `Rep.down`, `Rep.downSES`: the kernel of `Ind_⊥^G A ⟶ A` and its short exact sequence.
* `groupCohomology.upIso`, `groupCohomology.upResIso`: `Hⁿ⁺¹(S, up A) ≅ Hⁿ⁺²(S, A)`.
* `TauCeti.TateCohomology.upIso`, `TauCeti.TateCohomology.upResIso`: `Ĥⁿ(S, up A) ≅ Ĥⁿ⁺¹(S, A)`.
* `TauCeti.TateCohomology.downIso`, `TauCeti.TateCohomology.downResIso`:
  `Ĥⁿ(S, A) ≅ Ĥⁿ⁺¹(S, down A)`.

## Main statements

* `Rep.upSES_shortExact`, `Rep.upSES_res_shortExact`, `Rep.downSES_shortExact`,
  `Rep.downSES_res_shortExact`: the dimension-shifting sequences are short exact, also after
  restriction.
* `groupCohomology.isIso_δ_upSES`, `groupCohomology.epi_δ_upSES_zero` and their restricted
  versions: the connecting homomorphisms are isomorphisms in positive degree and surjective in
  degree zero.
* `TauCeti.TateCohomology.isIso_δ_of_isZero`: a connecting homomorphism of Tate cohomology is an
  isomorphism when the middle term has vanishing Tate cohomology in the two relevant degrees.
* `groupCohomology.δ_comp_map_res`: the connecting homomorphism commutes with restriction along a
  group homomorphism.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §1.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §7.
-/

public noncomputable section

universe u

open CategoryTheory Limits

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-! ### The functor `up` -/

/-- The cokernel of the embedding `A ⟶ Coind_⊥^G A`, so that `Hⁿ⁺¹(G, up A) ≅ Hⁿ⁺²(G, A)`. -/
@[expose] def up (A : Rep k G) : Rep k G := cokernel (coindBotUnit A)

/-- The projection from the coinduced module onto `up A`. -/
@[expose] def upπ (A : Rep k G) : coindBot k G A.V ⟶ up A := cokernel.π (coindBotUnit A)

/-- The projection onto `up A` is an epimorphism. -/
instance upπ_epi (A : Rep k G) : Epi (upπ A) :=
  inferInstanceAs (Epi (cokernel.π (coindBotUnit A)))

/-- The short complex `A ⟶ Coind_⊥^G A ⟶ up A` defining `up A`. -/
@[expose, implicit_reducible] def upSES (A : Rep k G) : ShortComplex (Rep k G) :=
  .mk (coindBotUnit A) (upπ A) (cokernel.condition (coindBotUnit A))

/-- The first term of the short complex defining `up A` is `A`. -/
@[simp]
theorem upSES_X₁ (A : Rep k G) : (upSES A).X₁ = A := rfl

/-- The middle term of the short complex defining `up A` is the coinduced module. -/
@[simp]
theorem upSES_X₂ (A : Rep k G) : (upSES A).X₂ = coindBot k G A.V := rfl

/-- The last term of the short complex defining `up A` is `up A`. -/
@[simp]
theorem upSES_X₃ (A : Rep k G) : (upSES A).X₃ = up A := rfl

/-- The short complex `A ⟶ Coind_⊥^G A ⟶ up A` is short exact. -/
theorem upSES_shortExact (A : Rep k G) : (upSES A).ShortExact where
  exact := ShortComplex.exact_cokernel (coindBotUnit A)
  mono_f := inferInstanceAs (Mono (coindBotUnit A))
  epi_g := inferInstanceAs (Epi (upπ A))

/-- The short complex `A ⟶ Coind_⊥^G A ⟶ up A` stays short exact after restriction along any
group homomorphism `f : H →* G`. -/
theorem upSES_res_shortExact {H : Type u} [Group H] (f : H →* G) (A : Rep k G) :
    ((upSES A).map (resFunctor f)).ShortExact :=
  (shortExact_res f).2 (upSES_shortExact A)

/-- The map of coinduced representations induced by a map `f : A ⟶ B`: postcomposition with `f`
on functions `G → A`. -/
abbrev coindBotMap {A B : Rep k G} (f : A ⟶ B) : coindBot k G A.V ⟶ coindBot k G B.V :=
  (coindBotFunctor k G).map (ModuleCat.ofHom f.hom.toLinearMap)

/-- The map of coinduced representations induced by `f` applies `f` pointwise. -/
@[simp]
theorem coindBotMap_hom_apply_coe {A B : Rep k G} (f : A ⟶ B) (x : coindBot k G A.V) (g : G) :
    ((coindBotMap f).hom x).1 g = f.hom (x.1 g) := by
  rfl

/-- The embedding into the coinduced representation is natural in the representation. -/
@[reassoc]
theorem coindBotUnit_naturality {A B : Rep k G} (f : A ⟶ B) :
    f ≫ coindBotUnit B = coindBotUnit A ≫ coindBotMap f := by
  ext x g
  simp only [hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.coe_comp,
    Function.comp_apply, Representation.IntertwiningMap.coe_toLinearMap]
  rw [coindBotUnit_hom_apply_coe, coindBotMap_hom_apply_coe, coindBotUnit_hom_apply_coe]
  exact (hom_comm_apply f g x).symm

/-- The map `up A ⟶ up B` induced by `f : A ⟶ B`. -/
@[expose] def upMap {A B : Rep k G} (f : A ⟶ B) : up A ⟶ up B :=
  cokernel.map (coindBotUnit A) (coindBotUnit B) f (coindBotMap f) (coindBotUnit_naturality f).symm

/-- The projections onto `up` intertwine `coindBotMap f` and `upMap f`. -/
@[reassoc (attr := simp)]
theorem upπ_comp_upMap {A B : Rep k G} (f : A ⟶ B) :
    upπ A ≫ upMap f = coindBotMap f ≫ upπ B :=
  cokernel.π_desc _ _ _

/-- The morphism of short complexes `upSES A ⟶ upSES B` induced by `f : A ⟶ B`. -/
@[expose, simps]
def upSESMap {A B : Rep k G} (f : A ⟶ B) : upSES A ⟶ upSES B where
  τ₁ := f
  τ₂ := coindBotMap f
  τ₃ := upMap f
  comm₁₂ := coindBotUnit_naturality f
  comm₂₃ := (upπ_comp_upMap f).symm

/-! ### The functor `down` -/

/-- The kernel of the projection `Ind_⊥^G A ⟶ A`, so that `Ĥⁿ(G, A) ≅ Ĥⁿ⁺¹(G, down A)`. -/
@[expose] def down (A : Rep k G) : Rep k G := kernel (indBotCounit A)

/-- The inclusion of `down A` into the induced module. -/
@[expose] def downι (A : Rep k G) : down A ⟶ indBot k G A.V := kernel.ι (indBotCounit A)

/-- The inclusion of `down A` is a monomorphism. -/
instance downι_mono (A : Rep k G) : Mono (downι A) :=
  inferInstanceAs (Mono (kernel.ι (indBotCounit A)))

/-- The short complex `down A ⟶ Ind_⊥^G A ⟶ A` defining `down A`. -/
@[expose, implicit_reducible] def downSES (A : Rep k G) : ShortComplex (Rep k G) :=
  .mk (downι A) (indBotCounit A) (kernel.condition (indBotCounit A))

/-- The first term of the short complex defining `down A` is `down A`. -/
@[simp]
theorem downSES_X₁ (A : Rep k G) : (downSES A).X₁ = down A := rfl

/-- The middle term of the short complex defining `down A` is the induced module. -/
@[simp]
theorem downSES_X₂ (A : Rep k G) : (downSES A).X₂ = indBot k G A.V := rfl

/-- The last term of the short complex defining `down A` is `A`. -/
@[simp]
theorem downSES_X₃ (A : Rep k G) : (downSES A).X₃ = A := rfl

/-- The short complex `down A ⟶ Ind_⊥^G A ⟶ A` is short exact. -/
theorem downSES_shortExact (A : Rep k G) : (downSES A).ShortExact where
  exact := ShortComplex.exact_kernel (indBotCounit A)
  mono_f := inferInstanceAs (Mono (downι A))
  epi_g := inferInstanceAs (Epi (indBotCounit A))

/-- The short complex `down A ⟶ Ind_⊥^G A ⟶ A` stays short exact after restriction along any
group homomorphism `f : H →* G`. -/
theorem downSES_res_shortExact {H : Type u} [Group H] (f : H →* G) (A : Rep k G) :
    ((downSES A).map (resFunctor f)).ShortExact :=
  (shortExact_res f).2 (downSES_shortExact A)

end Rep

namespace groupCohomology

open Rep

variable {k G : Type u} [CommRing k] [Group G]

/-! ### Dimension shifting in ordinary cohomology -/

/-- The connecting homomorphism `Hⁿ⁺¹(G, up A) ⟶ Hⁿ⁺²(G, A)` is an isomorphism. -/
theorem isIso_δ_upSES (A : Rep k G) (n : ℕ) :
    IsIso (δ (upSES_shortExact A) (n + 1) (n + 2) rfl) :=
  isIso_δ_of_isZero _ _ (isZero_coindBot_succ A.V n) (isZero_coindBot_succ A.V (n + 1))

/-- The connecting homomorphism `H⁰(G, up A) ⟶ H¹(G, A)` is surjective. -/
theorem epi_δ_upSES_zero (A : Rep k G) : Epi (δ (upSES_shortExact A) 0 1 rfl) :=
  epi_δ_of_isZero _ 0 (isZero_coindBot_succ A.V 0)

/-- For a subgroup `S ≤ G`, the connecting homomorphism `Hⁿ⁺¹(S, up A) ⟶ Hⁿ⁺²(S, A)` is an
isomorphism. -/
theorem isIso_δ_upSES_res (S : Subgroup G) (A : Rep k G) (n : ℕ) :
    IsIso (δ (upSES_res_shortExact S.subtype A) (n + 1) (n + 2) rfl) :=
  isIso_δ_of_isZero _ _ (isZero_res_coindBot_succ S A.V n)
    (isZero_res_coindBot_succ S A.V (n + 1))

/-- For a subgroup `S ≤ G`, the connecting homomorphism `H⁰(S, up A) ⟶ H¹(S, A)` is
surjective. -/
theorem epi_δ_upSES_res_zero (S : Subgroup G) (A : Rep k G) :
    Epi (δ (upSES_res_shortExact S.subtype A) 0 1 rfl) :=
  epi_δ_of_isZero _ 0 (isZero_res_coindBot_succ S A.V 0)

/-- Dimension shifting: `Hⁿ⁺¹(G, up A) ≅ Hⁿ⁺²(G, A)`, given by the connecting homomorphism. -/
def upIso (A : Rep k G) (n : ℕ) : groupCohomology (up A) (n + 1) ≅ groupCohomology A (n + 2) :=
  haveI := isIso_δ_upSES A n
  asIso (δ (upSES_shortExact A) (n + 1) (n + 2) rfl)

/-- The dimension-shifting isomorphism is the connecting homomorphism. -/
@[simp]
theorem upIso_hom (A : Rep k G) (n : ℕ) :
    (upIso A n).hom = δ (upSES_shortExact A) (n + 1) (n + 2) rfl := by
  rfl

/-- Dimension shifting after restriction to a subgroup `S ≤ G`:
`Hⁿ⁺¹(S, up A) ≅ Hⁿ⁺²(S, A)`, given by the connecting homomorphism. -/
def upResIso (S : Subgroup G) (A : Rep k G) (n : ℕ) :
    groupCohomology (res S.subtype (up A)) (n + 1) ≅ groupCohomology (res S.subtype A) (n + 2) :=
  haveI := isIso_δ_upSES_res S A n
  asIso (δ (upSES_res_shortExact S.subtype A) (n + 1) (n + 2) rfl)

/-- The restricted dimension-shifting isomorphism is the connecting homomorphism. -/
@[simp]
theorem upResIso_hom (S : Subgroup G) (A : Rep k G) (n : ℕ) :
    (upResIso S A n).hom = δ (upSES_res_shortExact S.subtype A) (n + 1) (n + 2) rfl := by
  rfl

/-! ### Restriction and the connecting homomorphism -/

/-- The connecting homomorphism of ordinary cohomology commutes with restriction along a group
homomorphism `f : H →* G`: `δ ≫ res = res ≫ δ`. -/
theorem δ_comp_map_res {H : Type u} [Group H] (f : H →* G) {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f (𝟙 (res f X.X₁)) j =
      map f (𝟙 (res f X.X₃)) i ≫ δ ((shortExact_res f).2 hX) i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality
    (S₁ := X.map (cochainsFunctor k G)) (S₂ := (X.map (resFunctor f)).map (cochainsFunctor k H))
    { τ₁ := cochainsMap f (𝟙 (res f X.X₁))
      τ₂ := cochainsMap f (𝟙 (res f X.X₂))
      τ₃ := cochainsMap f (𝟙 (res f X.X₃)) }
    (map_cochainsFunctor_shortExact hX) (map_cochainsFunctor_shortExact ((shortExact_res f).2 hX))
    i j hij

end groupCohomology

namespace TauCeti.TateCohomology

open Rep

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-! ### Dimension shifting in Tate cohomology -/

/-- A connecting homomorphism of Tate cohomology is an isomorphism when the middle term of the
short exact sequence has vanishing Tate cohomology in the two relevant degrees. -/
theorem isIso_δ_of_isZero {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℤ)
    (h₀ : IsZero (tateCohomology X.X₂ n)) (h₁ : IsZero (tateCohomology X.X₂ (n + 1))) :
    IsIso (_root_.TateCohomology.δ hX n) :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact hX).isIso_δ n (n + 1) rfl h₀ h₁

/-- The connecting homomorphism `Ĥⁿ(G, up A) ⟶ Ĥⁿ⁺¹(G, A)` is an isomorphism. -/
theorem isIso_δ_upSES (A : Rep k G) (n : ℤ) :
    IsIso (_root_.TateCohomology.δ (upSES_shortExact A) n) :=
  isIso_δ_of_isZero _ n (isZero_coindBot A.V n) (isZero_coindBot A.V (n + 1))

/-- The connecting homomorphism `Ĥⁿ(G, A) ⟶ Ĥⁿ⁺¹(G, down A)` is an isomorphism. -/
theorem isIso_δ_downSES (A : Rep k G) (n : ℤ) :
    IsIso (_root_.TateCohomology.δ (downSES_shortExact A) n) :=
  isIso_δ_of_isZero _ n (isZero_indBot A.V n) (isZero_indBot A.V (n + 1))

/-- Dimension shifting in Tate cohomology: `Ĥⁿ(G, up A) ≅ Ĥⁿ⁺¹(G, A)`, given by the connecting
homomorphism. -/
def upIso (A : Rep k G) (n : ℤ) : tateCohomology (up A) n ≅ tateCohomology A (n + 1) :=
  haveI := isIso_δ_upSES A n
  asIso (_root_.TateCohomology.δ (upSES_shortExact A) n)

/-- The Tate dimension-shifting isomorphism for `up` is the connecting homomorphism. -/
@[simp]
theorem upIso_hom (A : Rep k G) (n : ℤ) :
    (upIso A n).hom = _root_.TateCohomology.δ (upSES_shortExact A) n := by
  rfl

/-- Dimension shifting in Tate cohomology: `Ĥⁿ(G, A) ≅ Ĥⁿ⁺¹(G, down A)`, given by the
connecting homomorphism. -/
def downIso (A : Rep k G) (n : ℤ) : tateCohomology A n ≅ tateCohomology (down A) (n + 1) :=
  haveI := isIso_δ_downSES A n
  asIso (_root_.TateCohomology.δ (downSES_shortExact A) n)

/-- The Tate dimension-shifting isomorphism for `down` is the connecting homomorphism. -/
@[simp]
theorem downIso_hom (A : Rep k G) (n : ℤ) :
    (downIso A n).hom = _root_.TateCohomology.δ (downSES_shortExact A) n := by
  rfl

omit [Fintype G] in
/-- For a finite subgroup `S ≤ G`, the connecting homomorphism `Ĥⁿ(S, up A) ⟶ Ĥⁿ⁺¹(S, A)` is
an isomorphism. -/
theorem isIso_δ_upSES_res (S : Subgroup G) [Fintype S] (A : Rep k G) (n : ℤ) :
    IsIso (_root_.TateCohomology.δ (upSES_res_shortExact S.subtype A) n) :=
  isIso_δ_of_isZero _ n (isZero_res_coindBot S A.V n) (isZero_res_coindBot S A.V (n + 1))

omit [Fintype G] in
/-- For a subgroup `S` of a finite group `G`, the connecting homomorphism
`Ĥⁿ(S, A) ⟶ Ĥⁿ⁺¹(S, down A)` is an isomorphism. -/
theorem isIso_δ_downSES_res [Finite G] (S : Subgroup G) [Fintype S] (A : Rep k G) (n : ℤ) :
    IsIso (_root_.TateCohomology.δ (downSES_res_shortExact S.subtype A) n) :=
  isIso_δ_of_isZero _ n (isZero_res_indBot S A.V n) (isZero_res_indBot S A.V (n + 1))

omit [Fintype G] in
/-- Dimension shifting in Tate cohomology after restriction to a finite subgroup `S ≤ G`:
`Ĥⁿ(S, up A) ≅ Ĥⁿ⁺¹(S, A)`, given by the connecting homomorphism. -/
def upResIso (S : Subgroup G) [Fintype S] (A : Rep k G) (n : ℤ) :
    tateCohomology (res S.subtype (up A)) n ≅ tateCohomology (res S.subtype A) (n + 1) :=
  haveI := isIso_δ_upSES_res S A n
  asIso (_root_.TateCohomology.δ (upSES_res_shortExact S.subtype A) n)

omit [Fintype G] in
/-- The restricted Tate dimension-shifting isomorphism for `up` is the connecting
homomorphism. -/
@[simp]
theorem upResIso_hom (S : Subgroup G) [Fintype S] (A : Rep k G) (n : ℤ) :
    (upResIso S A n).hom = _root_.TateCohomology.δ (upSES_res_shortExact S.subtype A) n := by
  rfl

omit [Fintype G] in
/-- Dimension shifting in Tate cohomology after restriction to a subgroup `S` of a finite group
`G`: `Ĥⁿ(S, A) ≅ Ĥⁿ⁺¹(S, down A)`, given by the connecting homomorphism. -/
def downResIso [Finite G] (S : Subgroup G) [Fintype S] (A : Rep k G) (n : ℤ) :
    tateCohomology (res S.subtype A) n ≅ tateCohomology (res S.subtype (down A)) (n + 1) :=
  haveI := isIso_δ_downSES_res S A n
  asIso (_root_.TateCohomology.δ (downSES_res_shortExact S.subtype A) n)

omit [Fintype G] in
/-- The restricted Tate dimension-shifting isomorphism for `down` is the connecting
homomorphism. -/
@[simp]
theorem downResIso_hom [Finite G] (S : Subgroup G) [Fintype S] (A : Rep k G) (n : ℤ) :
    (downResIso S A n).hom = _root_.TateCohomology.δ (downSES_res_shortExact S.subtype A) n := by
  rfl

end TauCeti.TateCohomology
