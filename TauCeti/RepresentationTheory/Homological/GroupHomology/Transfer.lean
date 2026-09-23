/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Shapiro
public import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Transfer in group homology

Let `S` be a finite-index subgroup of a group `G`. Group homology has a transfer map

`H_n(G, M) ⟶ H_n(S, Resˢᴳ M)`.

Unlike the covariant map induced by the inclusion `S → G`, the transfer goes against the group
homomorphism. It is obtained from the unit `M ⟶ Indˢᴳ Resˢᴳ M` of the finite-index
adjunction, followed by Shapiro's isomorphism
`H_n(G, Indˢᴳ Resˢᴳ M) ≃ H_n(S, Resˢᴳ M)`. Transporting it across the negative-degree
comparison gives restriction in Tate cohomology below degree `-1`.

Followed by corestriction `H_n(S, Resˢᴳ M) ⟶ H_n(G, M)`, the map induced by the inclusion, the
transfer is multiplication by the index `[G : S]`. Read through Shapiro's isomorphism,
corestriction is the map induced by the counit `Indˢᴳ Resˢᴳ M ⟶ M`
(`TauCeti.groupHomology.indIso_inv_comp_map_counit`), and the unit followed by the counit is
`[G : S]`.

## Main definitions

* `TauCeti.groupHomology.transfer`: the transfer from a group to a finite-index subgroup.

## Main results

* `TauCeti.groupHomology.transfer_comp_indIso_inv`: through the inverse of Shapiro's isomorphism,
  transfer is the map induced by the unit of the finite-index adjunction.
* `TauCeti.groupHomology.transfer_comp_map_subtype_id`: corestriction after transfer is
  multiplication by the index `[G : S]`.
* `TauCeti.groupHomology.transfer_zero_H0π`: in degree zero, where group homology is the module of
  coinvariants, the transfer is the relative transfer `Representation.relTransfer`,
  `⟦m⟧ ↦ ⟦∑_{q ∈ G ⧸ S} q⁻¹ • m⟧`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, Sections 9–10.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6.
-/

public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.groupHomology

variable {R G : Type u} [CommRing R] [Group G]

open scoped Classical in
/-- The transfer in group homology from a group to a finite-index subgroup. It is the map induced
by the unit `M ⟶ Indˢᴳ Resˢᴳ M`, followed by the homological Shapiro isomorphism. -/
def transfer (M : Rep R G) (S : Subgroup G) [S.FiniteIndex] (n : ℕ) :
    _root_.groupHomology M n ⟶ _root_.groupHomology (Rep.res S.subtype M) n :=
  (_root_.groupHomology.functor R G n).map ((Rep.resIndAdjunction R S).unit.app M) ≫
    (_root_.groupHomology.indIso S (Rep.res S.subtype M) n).hom

open scoped Classical in
/-- Through the inverse of the homological Shapiro isomorphism, transfer is the map induced by
the unit of the finite-index induction--restriction adjunction. -/
@[reassoc (attr := simp)]
theorem transfer_comp_indIso_inv (M : Rep R G) (S : Subgroup G) [S.FiniteIndex] (n : ℕ) :
    transfer M S n ≫ (_root_.groupHomology.indIso S (Rep.res S.subtype M) n).inv =
      (_root_.groupHomology.functor R G n).map ((Rep.resIndAdjunction R S).unit.app M) :=
  -- Cancelling Shapiro's isomorphism against the definition, rather than rewriting with
  -- `Iso.hom_inv_id`: the two occurrences of `Resˢᴳ M` carry different `Monoid ↥S` instances, so
  -- the rewrite does not match syntactically, while this equation holds by `rfl`.
  (Iso.comp_inv_eq _).2 rfl

open scoped Classical in
/-- **Corestriction after transfer is multiplication by the index**: for a finite-index subgroup
`S ≤ G`, the composite `Hₙ(G, M) ⟶ Hₙ(S, Res_S M) ⟶ Hₙ(G, M)` of the transfer and corestriction
is `[G : S]` times the identity, in every degree `n`. -/
@[reassoc, elementwise]
theorem transfer_comp_map_subtype_id (M : Rep R G) (S : Subgroup G) [S.FiniteIndex] (n : ℕ) :
    transfer M S n ≫ _root_.groupHomology.map S.subtype (𝟙 (Rep.res S.subtype M)) n =
      S.index • 𝟙 _ := by
  have hsmul : _root_.groupHomology.map (MonoidHom.id G) (S.index • 𝟙 M) n =
      (HomologicalComplex.homologyFunctor _ _ n).map
        ((_root_.groupHomology.chainsFunctor R G).map (S.index • 𝟙 M)) := by
    rw [_root_.groupHomology.map, HomologicalComplex.homologyFunctor_map,
      _root_.groupHomology.chainsFunctor_map]
    rfl
  rw [← TauCeti.groupHomology.indIso_inv_comp_map_counit, transfer_comp_indIso_inv_assoc,
    _root_.groupHomology.functor_map, ← _root_.groupHomology.map_id_comp,
    TauCeti.Rep.resIndAdjunction_unit_app_comp_indResAdjunction_counit_app,
    hsmul, Functor.map_nsmul, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  exact congrArg (S.index • ·) (CategoryTheory.Functor.map_id _ _)

section DegreeZero

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

-- In the `G`-coinvariants of an induced representation `Ind_S^G A`, the class of `⟦h ⊗ a⟧` does
-- not depend on `h ∈ G`: the element is `h⁻¹` acting on `⟦1 ⊗ a⟧`.
private theorem coinvariantsMk_indVMk (S : Subgroup G) (A : Rep R S) (h : G) (a : A.V) :
    Representation.Coinvariants.mk (Representation.ind S.subtype A.ρ)
        (Representation.IndV.mk S.subtype A.ρ h a) =
      Representation.Coinvariants.mk (Representation.ind S.subtype A.ρ)
        (Representation.IndV.mk S.subtype A.ρ 1 a) := by
  have hmk : Representation.IndV.mk S.subtype A.ρ h a =
      Representation.ind S.subtype A.ρ h⁻¹ (Representation.IndV.mk S.subtype A.ρ 1 a) := by
    rw [Representation.ind_mk, one_mul, inv_inv]
  rw [hmk, Representation.Coinvariants.mk_self_apply]

-- In the `G`-coinvariants of an induced representation `Ind_S^G A`, acting by `s ∈ S` on the
-- second factor of `⟦1 ⊗ a⟧` does not change its class: `⟦1 ⊗ s • a⟧ = ⟦s⁻¹ ⊗ a⟧` in `Ind_S^G A`,
-- and `coinvariantsMk_indVMk` removes the `s⁻¹`.
private theorem coinvariantsMk_indVMk_one_apply (S : Subgroup G) (A : Rep R S) (s : S) (a : A.V) :
    Representation.Coinvariants.mk (Representation.ind S.subtype A.ρ)
        (Representation.IndV.mk S.subtype A.ρ 1 (A.ρ s a)) =
      Representation.Coinvariants.mk (Representation.ind S.subtype A.ρ)
        (Representation.IndV.mk S.subtype A.ρ 1 a) := by
  have hbal : Representation.IndV.mk S.subtype A.ρ 1 (A.ρ s a) =
      Representation.IndV.mk S.subtype A.ρ (s⁻¹ : S) a := by
    -- `IndV.mk S.subtype A.ρ h a` is the class of `single h 1 ⊗ₜ a` in the coinvariants of the
    -- tensor product, where `mk_tmul_inv` moves `s⁻¹` from the left factor to the right one.
    simpa only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      InvMemClass.coe_inv, inv_inv, MonoidHom.coe_comp, Subgroup.coe_subtype,
      Representation.ofMulAction_single, smul_eq_mul, mul_one] using
      Representation.Coinvariants.mk_tmul_inv ((Representation.leftRegular R G).comp S.subtype)
        A.ρ (MonoidAlgebra.single 1 1) a s⁻¹
  rw [hbal, coinvariantsMk_indVMk]

open scoped Classical in
/-- **The unit of `Res ⊣ Ind`, read in coinvariants, is the relative transfer.** For a
finite-index subgroup `S ≤ G`, the unit `M ⟶ Ind_S^G Res_S M` sends `m` to `∑ᵢ ⟦gᵢ ⊗ gᵢ • m⟧` over
right coset representatives `gᵢ`; in the `G`-coinvariants of `Ind_S^G Res_S M` this is the class
of `⟦1 ⊗ ∑_{q ∈ G ⧸ S} q⁻¹ • m⟧`. The right coset `S g` is matched with the left coset `g⁻¹ S`,
and each summand depends only on its coset. -/
theorem coinvariantsMk_coindToInd_unit (M : Rep R G) (S : Subgroup G) [S.FiniteIndex]
    (m : M.V) :
    Representation.Coinvariants.mk (Representation.ind S.subtype (res S.subtype M).ρ)
        (coindToInd (res S.subtype M) (((resCoindAdjunction R S.subtype).unit.app M).hom m)) =
      Representation.Coinvariants.mk (Representation.ind S.subtype (res S.subtype M).ρ)
        (Representation.IndV.mk S.subtype (res S.subtype M).ρ 1
          (Representation.relTransfer M.ρ S m)) := by
  rw [coindToInd_apply, map_sum, Representation.relTransfer_apply, map_sum, map_sum]
  refine Fintype.sum_equiv (QuotientGroup.quotientRightRelEquivQuotientLeftRel S) _ _
    fun c => ?_
  induction c using Quotient.inductionOn with
  | h g =>
    set q : G ⧸ S := QuotientGroup.quotientRightRelEquivQuotientLeftRel S (Quotient.mk _ g)
      with hq
    have hq' : q = ((g⁻¹ : G) : G ⧸ S) := rfl
    have hs : (q.out : G)⁻¹ * g⁻¹ ∈ S := QuotientGroup.eq.mp (q.out_eq'.trans hq')
    have hg : (q.out : G)⁻¹ = ((⟨_, hs⟩ : S) : G) * g := by simp
    have h1 := coinvariantsMk_indVMk S (res S.subtype M) g (M.ρ g m)
    have h2 := coinvariantsMk_indVMk_one_apply S (res S.subtype M) ⟨_, hs⟩ (M.ρ g m)
    rw [hg, map_mul, Module.End.mul_apply]
    exact h1.trans h2.symm

open scoped Classical in
/-- **In degree zero, the transfer is the relative transfer on coinvariants.** Group homology in
degree zero is the module of coinvariants, and the transfer `H₀(G, M) ⟶ H₀(S, Res_S M)` sends the
class of `m` to the class of `∑_{q ∈ G ⧸ S} q⁻¹ • m`, the relative transfer
`Representation.relTransfer`. -/
theorem transfer_zero_H0π (M : Rep R G) (S : Subgroup G) [S.FiniteIndex] (m : M.V) :
    transfer M S 0 (_root_.groupHomology.H0π M m) =
      _root_.groupHomology.H0π (Rep.res S.subtype M) (Representation.relTransfer M.ρ S m) := by
  -- Shapiro's inverse is injective and is the change-of-group map along `S ≤ G` (`indIso_inv`),
  -- so it suffices to compare both sides as classes in `H₀(G, Ind_S^G Res_S M)`.
  apply (ModuleCat.mono_iff_injective
    (_root_.groupHomology.indIso S (Rep.res S.subtype M) 0).inv).1 inferInstance
  rw [← ModuleCat.comp_apply, transfer_comp_indIso_inv, indIso_inv]
  simp only [_root_.groupHomology.functor_map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, _root_.groupHomology.H0π_comp_map,
    _root_.groupHomology.H0π_comp_map]
  simp only [Functor.comp_obj]
  apply (ModuleCat.mono_iff_injective
    (_root_.groupHomology.H0Iso ((indFunctor R S.subtype).obj (res S.subtype M))).hom).1
    inferInstance
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, Category.assoc, Category.assoc,
    _root_.groupHomology.H0π_comp_H0Iso_hom, ModuleCat.comp_apply, ModuleCat.comp_apply]
  -- Both units are explicit by definition: `resIndAdjunction`'s goes through `coindToInd`, and
  -- `indResAdjunction`'s is `a ↦ ⟦1 ⊗ a⟧`.
  exact coinvariantsMk_coindToInd_unit M S m

end DegreeZero

end TauCeti.groupHomology
