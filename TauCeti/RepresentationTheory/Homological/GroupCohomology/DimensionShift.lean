/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Coinduced
public import TauCeti.RepresentationTheory.Induction.DimensionShift

/-!
# Dimension shifting in ordinary group cohomology

For a representation `A` of a group `G`, the upward dimension-shifting sequence

`0 ⟶ A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A ⟶ 0`

has a middle term whose cohomology vanishes in every positive degree (Shapiro's lemma). Its
connecting homomorphism is therefore an isomorphism `Hⁿ⁺¹(G, dimensionShiftUp A) ≅ Hⁿ⁺²(G, A)`,
and surjective in the remaining degree `H⁰(G, dimensionShiftUp A) ⟶ H¹(G, A)`. The same holds
after restriction to any subgroup, so a vanishing hypothesis can be moved between degrees
simultaneously on all subgroups, which is what the inflation-restriction sequence needs.

Only the upward sequence appears here. The downward sequence has `Ind_⊥^G A` as its middle term,
which is acyclic for ordinary cohomology only when `G` is finite; the downward shift is therefore
stated for Tate cohomology instead, in `TauCeti.TateCohomology.dimensionShiftDownIso`.

Each isomorphism below has Mathlib's `groupCohomology.δ` as its forward map, so its naturality is
the existing naturality of `δ` and no abstract choice of isomorphism enters.

## Main definitions

* `TauCeti.groupCohomology.dimensionShiftUpIso`, `dimensionShiftUpResIso`: the shift as an
  isomorphism, over `G` and after restriction to a subgroup.

## Main statements

* `TauCeti.groupCohomology.dimensionShiftUpIso_hom`, `dimensionShiftUpResIso_hom`: the shift is
  Mathlib's connecting homomorphism `groupCohomology.δ` of `Rep.dimensionShiftUpSES`.
* `TauCeti.groupCohomology.epi_δ_dimensionShiftUp_zero`,
  `TauCeti.groupCohomology.epi_δ_res_dimensionShiftUp_zero`: in the remaining degree the
  connecting homomorphism `H⁰(dimensionShiftUp A) ⟶ H¹(A)` is only surjective, over `G` and
  after restriction to a subgroup.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §1 (dimension shifting, 1.13).
-/

public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/-- **Dimension shifting** as an isomorphism: `Hⁿ⁺¹(G, dimensionShiftUp A) ≅ Hⁿ⁺²(G, A)`, the
connecting homomorphism of the coinduced sequence, whose middle term has vanishing cohomology
in both degrees (Shapiro's lemma). The forward map is Mathlib's `δ`, so naturality is free;
degree `0` is only an epimorphism, hence the indexing starts at `n + 1`. -/
def dimensionShiftUpIso (n : ℕ) :
    groupCohomology (dimensionShiftUp A) (n + 1) ≅ groupCohomology A (n + 2) :=
  (map_cochainsFunctor_shortExact (dimensionShiftUpSES_shortExact A)).δIso
    (n + 1) (n + 2) rfl (isZero_coindBot_succ A.V n) (isZero_coindBot_succ A.V (n + 1))

/-- The dimension-shifting isomorphism is the connecting homomorphism. -/
@[simp]
theorem dimensionShiftUpIso_hom (n : ℕ) : (dimensionShiftUpIso A n).hom =
    δ (dimensionShiftUpSES_shortExact A) (n + 1) (n + 2) rfl := (rfl)

/-- In the remaining degree the connecting homomorphism `H⁰(G, dimensionShiftUp A) ⟶ H¹(G, A)`
is surjective: Shapiro's lemma only gives vanishing of the coinduced middle term in positive
degrees, so degree `0` has the input an epimorphism needs but not the second input an
isomorphism would need. -/
theorem epi_δ_dimensionShiftUp_zero :
    Epi (δ (dimensionShiftUpSES_shortExact A) 0 1 rfl) :=
  epi_δ_of_isZero _ 0 (isZero_coindBot_succ A.V 0)

variable (S : Subgroup G)

/-- Dimension shifting after restriction to a subgroup, as an isomorphism:
`Hⁿ⁺¹(S, dimensionShiftUp A) ≅ Hⁿ⁺²(S, A)`. The forward map is Mathlib's `δ`, so naturality is
free; degree `0` is only an epimorphism, hence the indexing starts at `n + 1`. -/
def dimensionShiftUpResIso (n : ℕ) :
    groupCohomology (res S.subtype (dimensionShiftUp A)) (n + 1) ≅
      groupCohomology (res S.subtype A) (n + 2) :=
  (map_cochainsFunctor_shortExact
    (dimensionShiftUpSES_res_shortExact A S.subtype)).δIso (n + 1) (n + 2) rfl
      (isZero_res_coindBot_succ S A.V n) (isZero_res_coindBot_succ S A.V (n + 1))

/-- The restricted dimension-shifting isomorphism is the connecting homomorphism. -/
@[simp]
theorem dimensionShiftUpResIso_hom (n : ℕ) : (dimensionShiftUpResIso A S n).hom =
    δ (dimensionShiftUpSES_res_shortExact A S.subtype) (n + 1) (n + 2) rfl := (rfl)

/-- After restriction to a subgroup, the connecting homomorphism
`H⁰(S, dimensionShiftUp A) ⟶ H¹(S, A)` is surjective: Shapiro's lemma only gives vanishing of
the coinduced middle term in positive degrees, so degree `0` has the input an epimorphism needs
but not the second input an isomorphism would need. -/
theorem epi_δ_res_dimensionShiftUp_zero :
    Epi (δ (dimensionShiftUpSES_res_shortExact A S.subtype) 0 1 rfl) :=
  epi_δ_of_isZero _ 0 (isZero_res_coindBot_succ S A.V 0)

end TauCeti.groupCohomology
