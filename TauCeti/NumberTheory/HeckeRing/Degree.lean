/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import TauCeti.NumberTheory.HeckeRing.LeftCosetModule
public import TauCeti.NumberTheory.HeckeRing.Multiplication
public import TauCeti.NumberTheory.HeckeRing.Multiplicity.Unit
import Mathlib.Tactic.Group

/-!
# Hecke rings: the degree homomorphism

The degree of a double coset `HgH = ⊔ᵢ σᵢgH` is the number of left cosets in its
decomposition, `deg(HgH) = [H : H ∩ gHg⁻¹]`. Extended linearly it gives the degree
homomorphism `deg : 𝕋 Δ H R →+* R` of the Hecke ring (Proposition 3.3 of
[Shimura][shimura1971]). Multiplicativity is proved through the module of left cosets:
`deg f` is the coefficient sum of `f • [H]`, and the action satisfies the compatibility law
`(f * g) • m = g • (f • m)` (Proposition 3.4), so the coefficient sum multiplies.

Ported from the AINTLIB `LeanModularForms` project
(`HeckeRIngs/AbstractHeckeRing/Degree.lean` and the compatibility law of
`HeckeRIngs/AbstractHeckeRing/Associativity.lean`,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), per the
ModularForms roadmap's dependency policy; the compatibility law is stated as a plain lemma
(`HeckeLeftCosetModule.mul_smul'`) rather than through AINTLIB's reversed scalar action.

## Main definitions

* `HeckeCoset.degree D`: the number of left cosets in the decomposition of `D`.
* `HeckeCosetModule.coeffSum`: the coefficient-sum homomorphism of the left-coset module.
* `HeckeCosetModule.deg`: the degree homomorphism `𝕋 Δ H R →+* R`.

## Main results

* `HeckeLeftCoset.smulOrbit_card`: the orbit of a left coset under `D` has `D.degree`
  elements.
* `HeckeLeftCosetModule.mul_smul'`: the action compatibility `(f * g) • m = g • (f • m)`.
* `HeckeCosetModule.deg_mul`: the degree is multiplicative.
-/

public section

open DoubleCoset Subgroup

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G}

namespace HeckeCoset

variable [IsHeckeTriple Δ H H]

/-- The degree of a double coset: the number of left cosets `σᵢgH` in the decomposition
`HgH = ⊔ᵢ σᵢgH`, i.e. `[H : H ∩ gHg⁻¹]`. -/
noncomputable def degree (D : HeckeCoset Δ H H) : ℕ :=
  Fintype.card (DecompQuotient H H (D.rep : G))

/-- Every double coset has positive degree. -/
lemma degree_pos (D : HeckeCoset Δ H H) : 0 < D.degree :=
  Fintype.card_pos

/-- The identity double coset has degree one. -/
@[simp] lemma degree_one : (1 : HeckeCoset Δ H H).degree = 1 := by
  have hsub : Subsingleton (DecompQuotient H H ((1 : HeckeCoset Δ H H).rep : G)) :=
    subsingleton_decompQuotient_of_mem (rep_one_mem)
  exact Fintype.card_eq_one_iff_nonempty_unique.mpr
    ⟨uniqueOfSubsingleton (Classical.arbitrary _)⟩

end HeckeCoset

namespace HeckeCoset

variable [IsHeckeTriple Δ H H]

/-- The orbit of a left coset under the representative of `D` has `D.degree` elements. -/
lemma smulOrbit_rep_card (D : HeckeCoset Δ H H) (β : Δ) :
    (smulOrbit H D.rep β).card = D.degree :=
  smulOrbit_card D.rep β

end HeckeCoset

namespace HeckeLeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule

variable [IsHeckeTriple Δ H H] {R : Type*} [Semiring R]

variable (Δ H R) in
/-- The coefficient-sum homomorphism of the left-coset module: the sum of all coefficients
of a formal linear combination of left cosets. -/
noncomputable def coeffSum : (HeckeCoset Δ ⊥ H →₀ R) →+ R :=
  Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id R

omit [IsHeckeTriple Δ H H] in
@[simp] lemma coeffSum_single (q : HeckeCoset Δ ⊥ H) (b : R) :
    coeffSum Δ H R (Finsupp.single q b) = b :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- The coefficient sum of the action of a ring basis element on a module basis element:
the degree of the double coset appears as the orbit size. -/
lemma coeffSum_single_smul_single (D : HeckeCoset Δ H H) (q : HeckeCoset Δ ⊥ H) (a b : R) :
    coeffSum Δ H R (HeckeCosetModule.single R D a • (Finsupp.single q b :
      HeckeCoset Δ ⊥ H →₀ R)) = (D.degree : ℕ) • (a * b) := by
  classical
  rw [single_smul_single, map_sum]
  simp [smulOrbit_rep_card]

end HeckeLeftCosetModule

namespace HeckeLeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule

variable [IsHeckeTriple Δ H H] {R : Type*} [Semiring R]

/-- The action is `R`-homogeneous in the Hecke-ring argument. -/
lemma smul_smul_assoc (r : R) (t : 𝕋 Δ H R) (m : HeckeCoset Δ ⊥ H →₀ R) :
    (r • t) • m = r • (t • m) := by
  classical
  simp only [smul_eq_sum]
  refine (Finsupp.sum_smul_index fun D ↦ ?_).trans ?_
  · exact Finsupp.sum_congr (g2 := fun _ _ ↦ 0) (fun q _ ↦ Finset.sum_eq_zero fun i _ ↦ by
      simp) |>.trans (Finsupp.sum_fun_zero m)
  · refine Eq.trans (Finsupp.sum_congr fun D b₁ ↦ ?_) Finsupp.smul_sum.symm
    refine Eq.trans (Finsupp.sum_congr fun q b₂ ↦ ?_) Finsupp.smul_sum.symm
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [Finsupp.smul_single, smul_eq_mul, mul_assoc]

end HeckeLeftCosetModule

namespace HeckeLeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule

variable [IsHeckeTriple Δ H H] {R : Type*} [CommSemiring R]

/-- Over a commutative semiring, the action commutes with scalars in the module
argument. -/
lemma smul_comm' (r : R) (t : 𝕋 Δ H R) (m : HeckeCoset Δ ⊥ H →₀ R) :
    t • (r • m) = r • (t • m) := by
  classical
  simp only [smul_eq_sum]
  refine Eq.trans (Finsupp.sum_congr fun D b₁ ↦ ?_) Finsupp.smul_sum.symm
  refine Eq.trans (Finsupp.sum_smul_index fun q ↦ ?_) ?_
  · exact Finset.sum_eq_zero fun i _ ↦ by simp
  · refine Eq.trans (Finsupp.sum_congr fun q b₂ ↦ ?_) Finsupp.smul_sum.symm
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finsupp.smul_single, smul_eq_mul, mul_left_comm]

end HeckeLeftCosetModule

namespace HeckeLeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule Pointwise

variable [IsHeckeTriple Δ H H] {R : Type*} [Semiring R]

/-- The scalar operations distribute over finite sums of module elements. -/
private lemma smul_finset_sum {ι : Type*} (t : 𝕋 Δ H R) (s : Finset ι)
    (f : ι → (HeckeCoset Δ ⊥ H →₀ R)) : t • ∑ i ∈ s, f i = ∑ i ∈ s, t • f i := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, smul_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, smul_add, ih]

/-- Iterated action of two basis elements of the Hecke ring on a basis element of the
module: the double sum over the two orbit layers. -/
private lemma single_smul_single_smul (D₁ D₂ : HeckeCoset Δ H H) (q : HeckeCoset Δ ⊥ H)
    (a b c : R) :
    HeckeCosetModule.single R D₂ b •
        (HeckeCosetModule.single R D₁ a • (Finsupp.single q c : HeckeCoset Δ ⊥ H →₀ R)) =
      ∑ i ∈ smulOrbit H D₁.rep q.rep, ∑ j ∈ smulOrbit H D₂.rep i.rep,
        Finsupp.single j (b * (a * c)) := by
  rw [single_smul_single, smul_finset_sum]
  exact Finset.sum_congr rfl fun i _ ↦ single_smul_single D₂ i b (a * c)

/-- Expansion of the action of a structure-constants element: the multiplicity-weighted
orbit sums. -/
private lemma structureConstants_smul_single (D₁ D₂ : HeckeCoset Δ H H)
    (q : HeckeCoset Δ ⊥ H) (c : R) :
    HeckeCosetModule.structureConstants R H H H D₁.rep D₂.rep •
        (Finsupp.single q c : HeckeCoset Δ ⊥ H →₀ R) =
      (HeckeCosetModule.structureConstants R H H H D₁.rep D₂.rep).sum fun D mD ↦
        ∑ i ∈ smulOrbit H D.rep q.rep, Finsupp.single i (mD * c) := by
  rw [smul_eq_sum]
  exact Finsupp.sum_congr fun D _ ↦ Finsupp.sum_single_index (by simp)

omit [IsHeckeTriple Δ H H] in
open Classical in
/-- Evaluating a sum of distinct basis singles: the indicator coefficient. -/
private lemma sum_single_apply (s : Finset (HeckeCoset Δ ⊥ H)) (v : R)
    (x : HeckeCoset Δ ⊥ H) :
    (∑ i ∈ s, Finsupp.single i v : HeckeCoset Δ ⊥ H →₀ R) x = if x ∈ s then v else 0 := by
  classical
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' s x fun _ ↦ v]

open Classical in
/-- Coefficient of the double orbit sum at a left coset: the number of intermediate cosets
whose second-layer orbit contains it. -/
private lemma sum_sum_single_apply (g₁ g₂ β : Δ) (c : R) (x : HeckeCoset Δ ⊥ H) :
    (∑ i ∈ smulOrbit H g₁ β, ∑ j ∈ smulOrbit H g₂ i.rep,
        Finsupp.single j c : HeckeCoset Δ ⊥ H →₀ R) x =
      ((smulOrbit H g₁ β).filter fun i ↦ x ∈ smulOrbit H g₂ i.rep).card • c := by
  rw [Finset.sum_apply']
  calc ∑ i ∈ smulOrbit H g₁ β, (∑ j ∈ smulOrbit H g₂ i.rep, Finsupp.single j c) x
      = ∑ i ∈ smulOrbit H g₁ β, if x ∈ smulOrbit H g₂ i.rep then c else 0 :=
        Finset.sum_congr rfl fun i _ ↦ sum_single_apply _ c x
    _ = _ := by rw [← Finset.sum_filter, Finset.sum_const]

open Classical in
/-- Coefficient of a multiplicity-weighted orbit sum at a left coset: the weight of the
unique double coset whose orbit contains it, if any. -/
private lemma sum_smulOrbit_single_apply (t : 𝕋 Δ H R) (β : Δ) (c : R)
    (x : HeckeCoset Δ ⊥ H) :
    ((t.sum fun D mD ↦ ∑ i ∈ smulOrbit H D.rep β, Finsupp.single i (mD * c)) :
        HeckeCoset Δ ⊥ H →₀ R) x =
      t.sum fun D mD ↦ if x ∈ smulOrbit H D.rep β then mD * c else 0 := by
  exact Finsupp.sum_apply.trans (Finsupp.sum_congr fun D _ ↦ sum_single_apply _ _ x)

/-- A left coset lies in the orbit of at most one double coset. -/
private lemma eq_of_mem_smulOrbit {g₁ g₂ β : Δ} {x : HeckeCoset Δ ⊥ H}
    (h₁ : x ∈ smulOrbit H g₁ β) (h₂ : x ∈ smulOrbit H g₂ β) :
    HeckeCoset.mk H H g₁ = HeckeCoset.mk H H g₂ := by
  by_contra hne
  exact Finset.disjoint_left.mp (smulOrbit_disjoint β hne) h₁ h₂

open Classical in
/-- The weighted orbit indicator collapses to the containing double coset's weight. -/
private lemma sum_ite_orbit_eq (t : 𝕋 Δ H R) (β : Δ) (c : R) {x : HeckeCoset Δ ⊥ H}
    {D₀ : HeckeCoset Δ H H} (hx : x ∈ smulOrbit H D₀.rep β) :
    (t.sum fun D mD ↦ if x ∈ smulOrbit H D.rep β then mD * c else 0) = t D₀ * c := by
  refine (Finsupp.sum_eq_single D₀ (fun D _ hne ↦ ?_) (fun _ ↦ by simp)).trans (if_pos hx)
  rw [if_neg]
  intro hmem
  exact hne (by
    have h := eq_of_mem_smulOrbit hmem hx
    rwa [HeckeCoset.mk_rep, HeckeCoset.mk_rep] at h)

open Classical in
/-- Membership in the orbit through the canonical representative: `x` lies in the orbit of
`g` on `w` iff `w⁻¹ · x.rep` lies in the double coset `HgH`. -/
private lemma mem_smulOrbit_iff_rep {g w : Δ} {x : HeckeCoset Δ ⊥ H} :
    x ∈ smulOrbit H g w ↔
      ((w : G))⁻¹ * ((x.rep : Δ) : G) ∈ doubleCoset (g : G) (H : Set G) H := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_smulOrbit.mp hx
    have hrep := mk_bot_eq_mk_bot.mp ((HeckeCoset.mk_rep x).trans hi.symm)
    -- hrep : x.rep⁻¹ · (w·σᵢ·g) ∈ H, so w⁻¹·x.rep = σᵢ·g·(w·σᵢ·g)⁻¹·x.rep with σᵢ ∈ H
    refine mem_doubleCoset.mpr ⟨(i.out : G), i.out.2,
      (((x.rep : Δ) : G)⁻¹ * ((w : G) * (i.out : G) * (g : G)))⁻¹, H.inv_mem hrep, by group⟩
  · intro hmem
    obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := mem_doubleCoset.mp hmem
    set i : DecompQuotient H H (g : G) := QuotientGroup.mk ⟨h₁, hh₁⟩ with hi
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct (g : G) • H).subgroupOf H) (⟨h₁, hh₁⟩ : H)
    have hout : ((i.out : H) : G) = h₁ * n := by
      rw [hi]
      simpa [Subgroup.coe_mul] using congrArg (Subtype.val : H → G) hn
    refine mem_smulOrbit.mpr ⟨i, ?_⟩
    rw [← HeckeCoset.mk_rep x]
    refine mk_bot_eq_mk_bot.mpr ?_
    -- as in `smulOrbit_subset`, the setoid membership is stated through the coercions
    change ((w : G) * ((i.out : H) : G) * (g : G))⁻¹ * ((x.rep : Δ) : G) ∈ H
    have key : ((w : G) * ((i.out : H) : G) * (g : G))⁻¹ * ((x.rep : Δ) : G) =
        ((g : G)⁻¹ * (n : G)⁻¹ * g) * h₂ := by
      have hx : ((x.rep : Δ) : G) = (w : G) * (h₁ * (g : G) * h₂) := by
        rw [← heq]; group
      rw [hout, hx]
      group
    rw [key]
    exact H.mul_mem
      (by simpa [mul_assoc] using H.inv_mem (conj_mem_of_stabilizer (g : G) n)) hh₂

end HeckeLeftCosetModule
