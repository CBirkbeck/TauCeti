/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.LinearAlgebra.End.FiniteOrder
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Joint eigenvectors of commuting semisimple families

The eigenvalue function of a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` is a character: it maps `1` to `1`, is multiplicative, and — for
a finite group — valued in units, assembling into `charHomOfJointEigenvector : G →* Kˣ`.
Together with semisimplicity of finite-order endomorphisms in characteristic zero, this
yields the simultaneous-diagonalization toolkit for a commuting family of semisimple
endomorphisms: the joint eigenspaces are supremum-independent, they span (over an
algebraically closed field, in finite dimension), and every invariant submodule is the
supremum of its intersections with them.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/CharacterDecomp.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), extracted as
representation-theoretic infrastructure with no modular-forms dependence; it underlies the
nebentypus decomposition in `TauCeti/NumberTheory/ModularForms/CharacterDecomp.lean`.

## Main results

* `charHomOfJointEigenvector`: the eigenvalue function of a nonzero joint eigenvector of a
  finite-group representation, as a monoid homomorphism `G →* Kˣ`.
* `Module.End.isSemisimple_of_isOfFinOrder`: finite-order endomorphisms are semisimple in
  characteristic zero.
* `iSupIndep_iInf_eigenspace_of_isSemisimple`,
  `iSup_iInf_eigenspace_eq_top_of_isSemisimple`,
  `iSup_inf_iInf_eigenspace_of_invariant`: joint eigenspaces of a commuting semisimple
  family are independent, exhaust the space, and decompose every invariant submodule.
-/

public section

noncomputable section

open Polynomial

variable {G K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Monoid

variable [Monoid G]

/-- If `v ≠ 0` is a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` with eigenvalues `χ g`, then the eigenvalue at the
identity is `1`. -/
lemma eigenvalue_one_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) : χ 1 = 1 := by
  have h1 := hv_mem 1
  rw [Module.End.mem_eigenspace_iff, map_one, Module.End.one_apply] at h1
  exact (smul_left_inj hv).mp (by rw [← h1, one_smul])

/-- If `v ≠ 0` is a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` with eigenvalues `χ g`, then the eigenvalues are
multiplicative: `χ (g₁ * g₂) = χ g₁ * χ g₂`. -/
lemma eigenvalue_mul_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g₁ g₂ : G) :
    χ (g₁ * g₂) = χ g₁ * χ g₂ := by
  have h := hv_mem (g₁ * g₂)
  rw [Module.End.mem_eigenspace_iff, map_mul] at h
  refine (smul_left_inj hv).mp ?_
  rw [← h, Module.End.mul_apply, Module.End.mem_eigenspace_iff.mp (hv_mem g₂), map_smul,
    Module.End.mem_eigenspace_iff.mp (hv_mem g₁), smul_smul, mul_comm (χ g₂) (χ g₁)]

/-- If `g` has finite order and `v ≠ 0` is a joint eigenvector with eigenvalues
`χ`, then `χ g ≠ 0`: the eigenvalue of a finite-order element is a root of
unity (hence a unit). -/
lemma eigenvalue_ne_zero_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) {g : G}
    (hg : IsOfFinOrder g) :
    χ g ≠ 0 := by
  obtain ⟨n, hnpos, hn⟩ := hg.exists_pow_eq_one
  intro hzero
  have hχ_pow : χ (g ^ n) = χ g ^ n :=
    map_pow (⟨⟨χ, eigenvalue_one_of_jointEigenvector ρ χ v hv hv_mem⟩,
      eigenvalue_mul_of_jointEigenvector ρ χ v hv hv_mem⟩ : G →* K) g n
  rw [hn, eigenvalue_one_of_jointEigenvector ρ χ v hv hv_mem, hzero,
    zero_pow hnpos.ne'] at hχ_pow
  exact one_ne_zero hχ_pow

end Monoid

section Group

variable [Group G]

/-- Given a joint eigenvector `v ≠ 0` for a monoid-hom representation
`ρ : G →* Module.End K V` of a *finite* group `G`, the eigenvalue function
`χ : G → K` factors through a monoid homomorphism `G →* Kˣ`. -/
def charHomOfJointEigenvector [Finite G] (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) : G →* Kˣ where
  toFun g := Units.mk0 (χ g)
    (eigenvalue_ne_zero_of_jointEigenvector ρ χ v hv hv_mem (isOfFinOrder_of_finite g))
  map_one' := Units.ext (eigenvalue_one_of_jointEigenvector ρ χ v hv hv_mem)
  map_mul' g₁ g₂ :=
    Units.ext (eigenvalue_mul_of_jointEigenvector ρ χ v hv hv_mem g₁ g₂)

@[simp]
lemma charHomOfJointEigenvector_coe [Finite G] (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g : G) :
    ((charHomOfJointEigenvector ρ χ v hv hv_mem g) : K) = χ g := (rfl)

/-- If the joint eigenspace of an eigenvalue function `χ` of a finite-group
representation is nonzero, then `χ` is (the underlying function of) a character
`G →* Kˣ`. -/
lemma exists_charHom_of_iInf_eigenspace_ne_bot [Finite G] {ρ : G →* Module.End K V}
    {χ : G → K} (hχ : ⨅ g, (ρ g).eigenspace (χ g) ≠ ⊥) :
    ∃ χ₀ : G →* Kˣ, (fun g ↦ ((χ₀ g) : K)) = χ := by
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hχ
  exact ⟨charHomOfJointEigenvector ρ χ v hv_ne ((Submodule.mem_iInf _).mp hv_mem), rfl⟩

/-- A finite-order endomorphism of a vector space over a characteristic-zero field is
semisimple; the `IsOfFinOrder` packaging of `TauCeti.End.isSemisimple_of_pow_eq_one`. -/
lemma Module.End.isSemisimple_of_isOfFinOrder [CharZero K] {f : Module.End K V}
    (hf : IsOfFinOrder f) : f.IsSemisimple := by
  obtain ⟨n, hnpos, hn⟩ := hf.exists_pow_eq_one
  exact TauCeti.End.isSemisimple_of_pow_eq_one (Nat.cast_ne_zero.mpr hnpos.ne') hn

/-- The joint eigenspaces of a pairwise-commuting family of semisimple endomorphisms,
indexed by their eigenvalue functions, are supremum-independent. -/
lemma iSupIndep_iInf_eigenspace_of_isSemisimple {ι : Type*} (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hss : ∀ i, (f i).IsSemisimple) :
    iSupIndep fun χ : ι → K ↦ ⨅ i, (f i).eigenspace (χ i) := by
  have heq (i : ι) (μ : K) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have h_mapsTo (i j : ι) (φ : K) : Set.MapsTo (f i) ((f j).maxGenEigenspace φ : Set V)
      ((f j).maxGenEigenspace φ : Set V) := by
    refine Module.End.mapsTo_maxGenEigenspace_of_comm ?_ φ
    rcases eq_or_ne j i with rfl | hij
    · exact Commute.refl _
    · exact hcomm hij
  simpa only [heq] using Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f h_mapsTo

/-- Over an algebraically closed field and in finite dimension, the joint eigenspaces of a
pairwise-commuting family of semisimple endomorphisms exhaust the space. -/
lemma iSup_iInf_eigenspace_eq_top_of_isSemisimple [IsAlgClosed K]
    [FiniteDimensional K V] {ι : Type*} (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hss : ∀ i, (f i).IsSemisimple) :
    (⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i)) = ⊤ := by
  have heq (i : ι) (μ : K) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  simpa only [heq] using
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      hcomm fun i ↦ by simpa only [heq] using (hss i).iSup_eigenspace_eq_top

/-- A submodule invariant under a pairwise-commuting family of semisimple endomorphisms
with exhausting eigenspaces is the supremum of its intersections with the joint
eigenspaces. -/
lemma iSup_inf_iInf_eigenspace_of_invariant {ι : Type*} [FiniteDimensional K V]
    (f : ι → Module.End K V) (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hss : ∀ i, (f i).IsSemisimple) (htop : ∀ i, ⨆ μ : K, (f i).eigenspace μ = ⊤)
    (p : Submodule K V) (hp : ∀ i, ∀ x ∈ p, f i x ∈ p) :
    (⨆ χ : ι → K, p ⊓ ⨅ i, (f i).eigenspace (χ i)) = p := by
  have hmax (i : ι) (μ : K) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  simp_rw [← hmax,
    fun χ : ι → K ↦ Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo
      (f := f) (μ := χ) p (fun i ↦ hp i),
    ← Submodule.map_iSup]
  suffices h_restrict_top :
      (⨆ χ : ι → K, ⨅ i,
        Module.End.maxGenEigenspace ((f i).restrict (hp i)) (χ i)) = ⊤ by
    rw [h_restrict_top, Submodule.map_top, Submodule.range_subtype]
  apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
  · intro i j hij
    refine LinearMap.ext fun ⟨x, _⟩ ↦ Subtype.ext ?_
    simpa only [Module.End.mul_apply, LinearMap.coe_restrict_apply] using
      LinearMap.congr_fun (hcomm hij).eq x
  · refine fun i ↦ Module.End.genEigenspace_restrict_eq_top (hp i) ?_
    simpa only [hmax] using htop i

end Group

end
