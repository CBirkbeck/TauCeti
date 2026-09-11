/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.DimensionShift

/-!
# Corestriction in group cohomology

For a subgroup `S` of finite index in `G` and a `G`-representation `A`, the corestriction (or
transfer) map `Cor : Hⁿ(S, A) ⟶ Hⁿ(G, A)` is defined in degree zero as the norm
`A^S → A^G`, `x ↦ ∑ g • x` over a set of left coset representatives `g` of `S`, and in higher
degrees by dimension shifting (Milne, *Class Field Theory*, II 1.29): the connecting
homomorphisms of `0 ⟶ A ⟶ Coind_⊥^G A ⟶ up A ⟶ 0` identify `Hⁿ⁺¹(-, A)` with `Hⁿ(-, up A)`
for `n ≥ 1`, and are surjective onto `H¹(-, A)` in degree `n = 0`. The composite `Cor ∘ Res` is
multiplication by the index `[G : S]` (Milne II 1.30).

The construction follows `ClassFieldTheory/Cohomology/Functors/Corestriction.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main definitions

* `Representation.coresInvariants`: the norm map `A^S →ₗ[k] A^G` along `G ⧸ S`.
* `groupCohomology.cores₀`, `groupCohomology.cores₁`: corestriction in degrees zero and one.
* `groupCohomology.cores`: corestriction `Hⁿ(S, A) ⟶ Hⁿ(G, A)` in every degree.

## Main statements

* `groupCohomology.cores_naturality`: corestriction is natural in the coefficients.
* `groupCohomology.δ_comp_cores_upSES`: corestriction commutes with the connecting homomorphisms
  of the dimension-shifting sequence.
* `groupCohomology.map_res_cores`: `Cor ∘ Res` is multiplication by `[G : S]` (Milne II 1.30).

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §1.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public noncomputable section

universe u v

open CategoryTheory Limits Rep

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace Representation

variable {k G : Type u} {V : Type v} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (S : Subgroup G) [S.FiniteIndex] (ρ : Representation k G V)

/-- The norm along `G ⧸ S` of an `S`-invariant vector is `G`-invariant: the sum
`∑ g • x` over left coset representatives `g` of `S` does not depend on the choice of
representatives, and `G` permutes the cosets. -/
theorem sum_out_apply_mem_invariants (x : V) (hx : x ∈ invariants (ρ.comp S.subtype)) :
    ∑ i : G ⧸ S, ρ i.out x ∈ ρ.invariants := by
  rw [mem_invariants] at hx ⊢
  intro g
  rw [map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun i ↦ ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (g * i.out)
  rw [MulAction.toPerm_apply, ← QuotientGroup.out_eq' i, MulAction.Quotient.smul_mk,
    QuotientGroup.out_eq', smul_eq_mul, hs, map_mul, map_mul, Module.End.mul_apply,
    Module.End.mul_apply]
  exact congrArg _ (congrArg _ (hx s).symm)

/-- The norm map `A^S →ₗ[k] A^G` along a finite-index subgroup `S ≤ G`, sending an `S`-invariant
vector `x` to `∑ g • x` over a set of left coset representatives `g` of `S` (Milne II 1.29). -/
def coresInvariants : invariants (ρ.comp S.subtype) →ₗ[k] ρ.invariants where
  toFun x := ⟨∑ i : G ⧸ S, ρ i.out x.1, sum_out_apply_mem_invariants S ρ x.1 x.2⟩
  map_add' x y := by ext; simp [Finset.sum_add_distrib]
  map_smul' r x := by ext; simp [Finset.smul_sum]

/-- The norm map along `G ⧸ S` sends `x` to `∑ g • x` over left coset representatives. -/
@[simp]
theorem coe_coresInvariants_apply (x : invariants (ρ.comp S.subtype)) :
    (coresInvariants S ρ x : V) = ∑ i : G ⧸ S, ρ i.out x := by
  rfl

end Representation

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex]

/-! ### Degree zero -/

/-- Corestriction in degree zero: the norm map `H⁰(S, A) = A^S ⟶ A^G = H⁰(G, A)` along
`G ⧸ S`. -/
def cores₀ (A : Rep k G) : groupCohomology (res S.subtype A) 0 ⟶ groupCohomology A 0 :=
  (H0Iso (res S.subtype A)).hom ≫ ModuleCat.ofHom (Representation.coresInvariants S A.ρ) ≫
    (H0Iso A).inv

/-- Under the identification of `H⁰` with invariants, degree-zero corestriction is the norm map
along `G ⧸ S`. -/
@[reassoc]
theorem cores₀_comp_H0Iso_hom (A : Rep k G) :
    cores₀ S A ≫ (H0Iso A).hom =
      (H0Iso (res S.subtype A)).hom ≫ ModuleCat.ofHom (Representation.coresInvariants S A.ρ) := by
  simp [cores₀]

/-- Degree-zero corestriction is natural in the coefficient representation. -/
@[reassoc]
theorem cores₀_naturality {A B : Rep k G} (f : A ⟶ B) :
    map (MonoidHom.id S) ((resFunctor S.subtype).map f) 0 ≫ cores₀ S B =
      cores₀ S A ≫ map (MonoidHom.id G) f 0 := by
  rw [← cancel_mono (H0Iso B).hom, Category.assoc, cores₀_comp_H0Iso_hom,
    map_id_comp_H0Iso_hom_assoc, Category.assoc, map_id_comp_H0Iso_hom,
    cores₀_comp_H0Iso_hom_assoc]
  ext x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    invariantsFunctor_map_hom, Representation.coe_coresInvariants_apply]
  erw [LinearMap.codRestrict_apply, LinearMap.codRestrict_apply]
  simp [map_sum, hom_comm_apply]

/-- The composite `Res ∘ Cor` in degree zero is multiplication by the index (Milne II 1.30 for
`r = 0`): for `x ∈ A^G`, `∑ g • x = [G : S] • x`. -/
theorem map_res_cores₀ (A : Rep k G) :
    map S.subtype (𝟙 (res S.subtype A)) 0 ≫ cores₀ S A = S.index • 𝟙 (groupCohomology A 0) := by
  rw [← cancel_mono (H0Iso A).hom, Category.assoc, cores₀_comp_H0Iso_hom]
  ext x
  have hx : ((H0Iso (res S.subtype A)).hom.hom ((map S.subtype (𝟙 (res S.subtype A)) 0).hom x) :
      A) = ((H0Iso A).hom.hom x : A) :=
    map_H0Iso_hom_f_apply S.subtype (𝟙 (res S.subtype A)) x
  have hinv := ((H0Iso A).hom x).2
  rw [Representation.mem_invariants] at hinv
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    Representation.coe_coresInvariants_apply, hx, hinv, Finset.sum_const, Finset.card_univ,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card, ModuleCat.hom_nsmul, ModuleCat.hom_id,
    LinearMap.smul_apply, LinearMap.id_apply, map_nsmul]
  rfl

/-! ### Degree one -/

/-- The map `H⁰(S, Coind_⊥^G A) ⟶ H⁰(S, up A) ⟶ H⁰(G, up A) ⟶ H¹(G, A)` vanishes; this lets
degree-one corestriction descend along the surjection `H⁰(S, up A) ⟶ H¹(S, A)`. -/
theorem map_upπ_comp_cores₀_comp_δ (A : Rep k G) :
    map (MonoidHom.id S) (A := res S.subtype (coindBot k G A.V))
        ((resFunctor S.subtype).map (upπ A)) 0 ≫
      (cores₀ S (up A) ≫ δ (upSES_shortExact A) 0 1 rfl) = 0 := by
  rw [← Category.assoc, cores₀_naturality, Category.assoc]
  convert comp_zero
  exact (map_cochainsFunctor_shortExact (upSES_shortExact A)).comp_δ 0 1 rfl

/-- Corestriction in degree one, defined by dimension shifting: it is the unique map making the
square with the connecting homomorphisms `H⁰(-, up A) ⟶ H¹(-, A)` and degree-zero
corestriction commute. -/
def cores₁ (A : Rep k G) : groupCohomology (res S.subtype A) 1 ⟶ groupCohomology A 1 :=
  have : Epi (mapShortComplex₃ (upSES_res_shortExact S.subtype A) rfl).g :=
    epi_δ_upSES_res_zero S A
  (mapShortComplex₃_exact (upSES_res_shortExact S.subtype A) rfl).desc
    (cores₀ S (up A) ≫ δ (upSES_shortExact A) 0 1 rfl) (map_upπ_comp_cores₀_comp_δ S A)

/-- The defining property of degree-one corestriction: it is compatible with the connecting
homomorphisms of the dimension-shifting sequence and degree-zero corestriction. -/
@[reassoc]
theorem δ_comp_cores₁ (A : Rep k G) :
    δ (upSES_res_shortExact S.subtype A) 0 1 rfl ≫ cores₁ S A =
      cores₀ S (up A) ≫ δ (upSES_shortExact A) 0 1 rfl :=
  have : Epi (mapShortComplex₃ (upSES_res_shortExact S.subtype A) rfl).g :=
    epi_δ_upSES_res_zero S A
  (mapShortComplex₃_exact (upSES_res_shortExact S.subtype A) rfl).g_desc _ _

/-! ### All degrees -/

/-- Corestriction `Cor : Hⁿ(S, A) ⟶ Hⁿ(G, A)` for a finite-index subgroup `S ≤ G`, defined in
degree zero as the norm along `G ⧸ S`, in degree one by descending along the connecting
homomorphism, and in degree `n + 2` by dimension shifting from degree `n + 1` for `up A`
(Milne II 1.29). -/
def cores : (A : Rep k G) → (n : ℕ) → (groupCohomology (res S.subtype A) n ⟶ groupCohomology A n)
  | A, 0 => cores₀ S A
  | A, 1 => cores₁ S A
  | A, n + 2 => (upResIso S A n).inv ≫ cores (up A) (n + 1) ≫ (upIso A n).hom

/-- In degree zero, corestriction is the norm along `G ⧸ S`. -/
@[simp]
theorem cores_zero (A : Rep k G) : cores S A 0 = cores₀ S A := by
  rfl

/-- In degree one, corestriction is the map descended along the connecting homomorphism. -/
@[simp]
theorem cores_one (A : Rep k G) : cores S A 1 = cores₁ S A := by
  rfl

/-- In degree `n + 2`, corestriction is obtained by dimension shifting from degree `n + 1`. -/
theorem cores_succ_succ (A : Rep k G) (n : ℕ) :
    cores S A (n + 2) = (upResIso S A n).inv ≫ cores S (up A) (n + 1) ≫ (upIso A n).hom := by
  rfl

/-- Corestriction is compatible with the connecting homomorphisms of the dimension-shifting
sequence `0 ⟶ A ⟶ Coind_⊥^G A ⟶ up A ⟶ 0`: in degree zero this is the defining property of
`cores₁`, and in higher degrees it holds by construction. -/
@[reassoc]
theorem δ_comp_cores_upSES (A : Rep k G) (n : ℕ) :
    δ (upSES_res_shortExact S.subtype A) n (n + 1) rfl ≫ cores S A (n + 1) =
      cores S (up A) n ≫ δ (upSES_shortExact A) n (n + 1) rfl := by
  cases n with
  | zero => exact δ_comp_cores₁ S A
  | succ n =>
    rw [cores_succ_succ, ← upResIso_hom, ← upIso_hom, Iso.hom_inv_id_assoc]

omit [S.FiniteIndex] in
/-- The connecting homomorphism `Hⁿ(S, up A) ⟶ Hⁿ⁺¹(S, A)` of the restricted dimension-shifting
sequence is an epimorphism in every degree. -/
theorem epi_δ_upSES_res (A : Rep k G) (n : ℕ) :
    Epi (δ (upSES_res_shortExact S.subtype A) n (n + 1) rfl) := by
  cases n with
  | zero => exact epi_δ_upSES_res_zero S A
  | succ n => exact (isIso_δ_upSES_res S A n).epi_of_iso _

/-- Corestriction is natural in the coefficient representation. -/
@[reassoc]
theorem cores_naturality {A B : Rep k G} (f : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id S) ((resFunctor S.subtype).map f) n ≫ cores S B n =
      cores S A n ≫ map (MonoidHom.id G) f n := by
  induction n generalizing A B with
  | zero => exact cores₀_naturality S f
  | succ n ih =>
    have := epi_δ_upSES_res S A n
    -- Naturality of the connecting homomorphisms for the restricted and unrestricted
    -- dimension-shifting sequences of `f`.
    have hS := δ_naturality (upSES_res_shortExact S.subtype A) (upSES_res_shortExact S.subtype B)
      ((resFunctor S.subtype).mapShortComplex.map (upSESMap f)) n (n + 1) rfl
    have hG := δ_naturality (upSES_shortExact A) (upSES_shortExact B) (upSESMap f) n (n + 1) rfl
    simp only [Functor.mapShortComplex_map_τ₁, Functor.mapShortComplex_map_τ₃, upSESMap_τ₁,
      upSESMap_τ₃] at hS hG
    rw [← cancel_epi (δ (upSES_res_shortExact S.subtype A) n (n + 1) rfl), ← Category.assoc, hS,
      Category.assoc, δ_comp_cores_upSES, ← Category.assoc, ih (upMap f), Category.assoc, ← hG,
      ← Category.assoc, ← δ_comp_cores_upSES, Category.assoc]

/-- The composite `Cor ∘ Res : Hⁿ(G, A) ⟶ Hⁿ(S, A) ⟶ Hⁿ(G, A)` is multiplication by the index
`[G : S]` (Milne II 1.30). -/
theorem map_res_cores (A : Rep k G) (n : ℕ) :
    map S.subtype (𝟙 (res S.subtype A)) n ≫ cores S A n = S.index • 𝟙 (groupCohomology A n) := by
  induction n generalizing A with
  | zero => exact map_res_cores₀ S A
  | succ n ih =>
    have : Epi (δ (upSES_shortExact A) n (n + 1) rfl) := by
      cases n with
      | zero => exact epi_δ_upSES_zero A
      | succ n => exact (isIso_δ_upSES A n).epi_of_iso _
    have h := δ_comp_map_res S.subtype (upSES_shortExact A) n (n + 1) rfl
    dsimp only [upSES_X₁, upSES_X₃] at h
    rw [← cancel_epi (δ (upSES_shortExact A) n (n + 1) rfl), ← Category.assoc, h,
      Category.assoc, δ_comp_cores_upSES, ← Category.assoc, ih, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul]
    erw [Category.id_comp]

end groupCohomology
