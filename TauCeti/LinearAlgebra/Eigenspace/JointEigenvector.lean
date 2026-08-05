/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Joint eigenvectors of commuting semisimple families

The eigenvalue function of a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` is a character: it maps `1` to `1`, is multiplicative, and, for
a group, valued in units, assembling into `charHomOfJointEigenvector : G →* Kˣ`. This
yields the simultaneous-diagonalization toolkit for a commuting family of semisimple
endomorphisms: the joint eigenspaces are supremum-independent, they span (over an
algebraically closed field, in finite dimension), and every invariant submodule is the
supremum of its intersections with them.

When `G` is a *finite commutative group* there is a second, unconditional route to the same
spanning statements. Averaging against the characters of `G` produces Fourier projectors onto
the joint eigenspaces, so they exhaust the whole space — and cut out every invariant submodule —
with no algebraic-closedness, finite-dimensionality or semisimplicity hypothesis; all that is
needed is enough roots of unity in `K` and `Nat.card G` invertible there.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/CharacterDecomp.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), extracted as
representation-theoretic infrastructure with no modular-forms dependence; it underlies the
nebentypus decomposition in `TauCeti/NumberTheory/ModularForms/CharacterDecomp.lean`.

## Main results

* `charHomOfJointEigenvector`: the eigenvalue function of a nonzero joint eigenvector of a
  group representation, as a monoid homomorphism `G →* Kˣ`.
* `iSupIndep_iInf_eigenspace_of_commute`,
  `iSup_iInf_eigenspace_eq_top_of_isSemisimple`,
  `iSup_inf_iInf_eigenspace_of_invariant`: joint eigenspaces of a commuting family are
  independent (with no further hypotheses), exhaust the space when semisimple, and
  decompose every invariant submodule — with the character-indexed forms (`…_charHom…`)
  for group representations.
* `iSup_iInf_eigenspace_charHom_eq_top_of_commGroup`,
  `iSup_inf_iInf_eigenspace_charHom_of_invariant_of_commGroup`: for a finite commutative `G`
  with `[HasEnoughRootsOfUnity K (Monoid.exponent G)]` and `[NeZero (Nat.card G : K)]`, the
  character eigenspaces span the whole space, and every invariant submodule is the supremum of
  its intersections with them — proved by finite-group Fourier projectors, so neither
  semisimplicity nor finite dimension is assumed.
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

end Monoid

section Group

variable [Group G]

/-- The eigenvalues of a nonzero joint eigenvector of a group representation are
nonzero: `χ g · χ g⁻¹ = χ 1 = 1`. -/
lemma eigenvalue_ne_zero_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g : G) :
    χ g ≠ 0 :=
  left_ne_zero_of_mul_eq_one (b := χ g⁻¹) (by
    rw [← eigenvalue_mul_of_jointEigenvector ρ χ v hv hv_mem, mul_inv_cancel,
      eigenvalue_one_of_jointEigenvector ρ χ v hv hv_mem])

/-- Given a joint eigenvector `v ≠ 0` for a monoid-hom representation
`ρ : G →* Module.End K V` of a group `G`, the eigenvalue function `χ : G → K`
factors through a monoid homomorphism `G →* Kˣ`. -/
def charHomOfJointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) : G →* Kˣ where
  toFun g := Units.mk0 (χ g)
    (eigenvalue_ne_zero_of_jointEigenvector ρ χ v hv hv_mem g)
  map_one' := Units.ext (eigenvalue_one_of_jointEigenvector ρ χ v hv hv_mem)
  map_mul' g₁ g₂ :=
    Units.ext (eigenvalue_mul_of_jointEigenvector ρ χ v hv hv_mem g₁ g₂)

@[simp]
lemma charHomOfJointEigenvector_apply (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g : G) :
    ((charHomOfJointEigenvector ρ χ v hv hv_mem g) : K) = χ g := (rfl)

/-- If the joint eigenspace of an eigenvalue function `χ` of a group representation is
nonzero, then `χ` is (the underlying function of) a character `G →* Kˣ`. -/
lemma exists_charHom_of_iInf_eigenspace_ne_bot {ρ : G →* Module.End K V}
    {χ : G → K} (hχ : ⨅ g, (ρ g).eigenspace (χ g) ≠ ⊥) :
    ∃ χ₀ : G →* Kˣ, (fun g ↦ ((χ₀ g) : K)) = χ := by
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hχ
  exact ⟨charHomOfJointEigenvector ρ χ v hv_ne ((Submodule.mem_iInf _).mp hv_mem), rfl⟩

/-- The joint eigenspaces of a pairwise-commuting family of endomorphisms, indexed by
their eigenvalue functions, are supremum-independent — with no semisimplicity assumption:
independence of the larger generalized eigenspaces transports down. -/
lemma iSupIndep_iInf_eigenspace_of_commute {ι : Type*} (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) :
    iSupIndep fun χ : ι → K ↦ ⨅ i, (f i).eigenspace (χ i) := by
  have h_mapsTo (i j : ι) (φ : K) : Set.MapsTo (f i) ((f j).maxGenEigenspace φ : Set V)
      ((f j).maxGenEigenspace φ : Set V) := by
    refine Module.End.mapsTo_maxGenEigenspace_of_comm ?_ φ
    rcases eq_or_ne j i with rfl | hij
    · exact Commute.refl _
    · exact hcomm hij
  exact (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f h_mapsTo).mono
    fun χ ↦ iInf_mono fun i ↦ Module.End.eigenspace_le_maxGenEigenspace

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

/-- A finite-dimensional submodule invariant under a pairwise-commuting family of
endomorphisms whose **restrictions** to it are semisimple is the supremum of its
intersections with the joint eigenspaces: the restricted family diagonalizes, with no
assumption on the ambient operators. -/
lemma iSup_inf_iInf_eigenspace_of_invariant [IsAlgClosed K] {ι : Type*}
    (f : ι → Module.End K V)
    (p : Submodule K V) [FiniteDimensional K p] (hp : ∀ i, ∀ x ∈ p, f i x ∈ p)
    (hcomm : Pairwise fun i j ↦ Commute ((f i).restrict (hp i)) ((f j).restrict (hp j)))
    (hss : ∀ i, Module.End.IsSemisimple ((f i).restrict (hp i))) :
    (⨆ χ : ι → K, p ⊓ ⨅ i, (f i).eigenspace (χ i)) = p := by
  have hmax' (i : ι) (μ : K) :
      Module.End.maxGenEigenspace ((f i).restrict (hp i)) μ =
        Module.End.eigenspace ((f i).restrict (hp i)) μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  -- the joint eigenspace intersected with `p` is the image of the restricted joint
  -- eigenspace, elementarily: evaluation of `f i` and its restriction agree on `p`
  have hbridge : ∀ χ : ι → K, p ⊓ (⨅ i, (f i).eigenspace (χ i)) =
      Submodule.map p.subtype
        (⨅ i, Module.End.eigenspace ((f i).restrict (hp i)) (χ i)) := by
    intro χ
    ext x
    constructor
    · rintro ⟨hxp, hxe⟩
      refine ⟨⟨x, hxp⟩, (Submodule.mem_iInf _).mpr fun i ↦ ?_, rfl⟩
      have hx := (Submodule.mem_iInf _).mp hxe i
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      exact Subtype.ext (by simpa [LinearMap.restrict_apply] using hx)
    · rintro ⟨⟨y, hyp⟩, hye, rfl⟩
      refine ⟨hyp, (Submodule.mem_iInf _).mpr fun i ↦ ?_⟩
      have hy := (Submodule.mem_iInf _).mp hye i
      rw [Module.End.mem_eigenspace_iff] at hy ⊢
      simpa [LinearMap.restrict_apply] using congrArg Subtype.val hy
  simp_rw [hbridge, ← Submodule.map_iSup]
  suffices h_restrict_top :
      (⨆ χ : ι → K, ⨅ i,
        Module.End.eigenspace ((f i).restrict (hp i)) (χ i)) = ⊤ by
    rw [h_restrict_top, Submodule.map_top, Submodule.range_subtype]
  exact iSup_iInf_eigenspace_eq_top_of_isSemisimple (fun i ↦ (f i).restrict (hp i))
    hcomm hss

section CharHom

variable {ρ : G →* Module.End K V}

/-- **Character-indexed spanning**: for a commuting semisimple representation of a group
over an algebraically closed field, in finite dimension, the joint eigenspaces indexed by
characters `G →* Kˣ` exhaust the space — eigenvalue functions that are not
characters contribute `⊥`. -/
lemma iSup_iInf_eigenspace_charHom_eq_top [IsAlgClosed K] [FiniteDimensional K V]
    (hcomm : Pairwise fun g₁ g₂ ↦ Commute (ρ g₁) (ρ g₂))
    (hss : ∀ g, (ρ g).IsSemisimple) :
    (⨆ χ₀ : G →* Kˣ, ⨅ g, (ρ g).eigenspace (χ₀ g)) = ⊤ := by
  have h := iSup_iInf_eigenspace_eq_top_of_isSemisimple (fun g ↦ ρ g) hcomm hss
  refine le_antisymm le_top (h ▸ iSup_le fun χ ↦ ?_)
  by_cases hχ : (⨅ g, (ρ g).eigenspace (χ g)) = ⊥
  · simp only [hχ, bot_le]
  · obtain ⟨χ₀, rfl⟩ := exists_charHom_of_iInf_eigenspace_ne_bot hχ
    exact le_iSup (fun ψ : G →* Kˣ ↦ ⨅ g, (ρ g).eigenspace (ψ g)) χ₀

/-- **Character-indexed independence** of the joint eigenspaces. -/
lemma iSupIndep_iInf_eigenspace_charHom
    (hcomm : Pairwise fun g₁ g₂ ↦ Commute (ρ g₁) (ρ g₂)) :
    iSupIndep fun χ₀ : G →* Kˣ ↦ ⨅ g, (ρ g).eigenspace (χ₀ g) :=
  (iSupIndep_iInf_eigenspace_of_commute (fun g ↦ ρ g) hcomm).comp
    fun _ _ h ↦ MonoidHom.ext fun g ↦ Units.ext (congr_fun h g)

/-- **Character-indexed decomposition of a finite-dimensional invariant submodule**,
assuming only that the restricted representation is semisimple. -/
lemma iSup_inf_iInf_eigenspace_charHom_of_invariant [IsAlgClosed K]
    (p : Submodule K V) [FiniteDimensional K p] (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p)
    (hcomm : Pairwise fun g₁ g₂ ↦
      Commute ((ρ g₁).restrict (hp g₁)) ((ρ g₂).restrict (hp g₂)))
    (hss : ∀ g, Module.End.IsSemisimple ((ρ g).restrict (hp g))) :
    (⨆ χ₀ : G →* Kˣ, p ⊓ ⨅ g, (ρ g).eigenspace (χ₀ g)) = p := by
  have h := iSup_inf_iInf_eigenspace_of_invariant (fun g ↦ ρ g) p hp hcomm hss
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) ?_
  conv_lhs => rw [← h]
  refine iSup_le fun χ ↦ ?_
  by_cases hχ : p ⊓ (⨅ g, (ρ g).eigenspace (χ g)) = ⊥
  · simp only [hχ, bot_le]
  · obtain ⟨χ₀, rfl⟩ := exists_charHom_of_iInf_eigenspace_ne_bot
      (fun h_bot ↦ hχ (by rw [h_bot, inf_bot_eq]))
    exact le_iSup (fun ψ : G →* Kˣ ↦ p ⊓ ⨅ g, (ρ g).eigenspace (ψ g)) χ₀

end CharHom

end Group

section FourierDecomposition

/-! ### Unconditional decomposition for finite commutative groups

For a finite commutative group `G` acting through `ρ : G →* Module.End K V` on any module
over a field with enough roots of unity — with no finite-dimensionality assumption — the
classical character projectors `|G|⁻¹ • ∑ d, χ(d)⁻¹ • ρ d` decompose every vector into
joint eigenvectors, so the joint eigenspaces indexed by `G →* Kˣ` span. -/

variable [CommGroup G] [Finite G]

private noncomputable instance : Fintype G :=
  Fintype.ofFinite _

private noncomputable instance : Fintype (G →* Kˣ) :=
  Fintype.ofFinite _

open Finset

variable {ρ : G →* Module.End K V}

-- the character projector applied to a vector
private noncomputable def fourierComponent (χ₀ : G →* Kˣ) (v : V) : V :=
  (Nat.card G : K)⁻¹ • ∑ d : G, (((χ₀ d)⁻¹ : Kˣ) : K) • ρ d v

variable (ρ) in
-- the projector lands in the joint eigenspace, by reindexing the averaged sum
private lemma fourierComponent_mem (χ₀ : G →* Kˣ) (v : V) (g : G) :
    fourierComponent (ρ := ρ) χ₀ v ∈ (ρ g).eigenspace (χ₀ g) := by
  rw [Module.End.mem_eigenspace_iff, fourierComponent, map_smul,
    smul_comm ((χ₀ g : Kˣ) : K) ((Nat.card G : K)⁻¹)]
  congr 1
  rw [map_sum]
  calc ∑ d : G, ρ g ((((χ₀ d)⁻¹ : Kˣ) : K) • ρ d v)
      = ∑ d : G, (((χ₀ d)⁻¹ : Kˣ) : K) • ρ (g * d) v := by
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        rw [map_smul, map_mul, Module.End.mul_apply]
    _ = ∑ e : G, (((χ₀ (g⁻¹ * e))⁻¹ : Kˣ) : K) • ρ e v := by
        exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun d ↦ by simp
    _ = (χ₀ g : K) • ∑ e : G, (((χ₀ e)⁻¹ : Kˣ) : K) • ρ e v := by
        rw [smul_sum]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [smul_smul]
        congr 1
        rw [map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]

variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

private instance : HasEnoughRootsOfUnity K (Monoid.exponent Gˣ) :=
  Monoid.exponent_eq_of_mulEquiv (toUnits (G := G)).symm ▸ inferInstance

-- the character group of a finite commutative group over a field with enough roots of
-- unity has the size of the group, by Mathlib's character duality
private lemma card_charHom : Nat.card (G →* Kˣ) = Nat.card G := by
  rw [Nat.card_congr (MulChar.equivToUnitHom.trans
      (toUnits (G := G)).monoidHomCongrLeftEquiv.symm).symm,
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity G K,
    Nat.card_congr (toUnits (G := G)).toEquiv.symm]

-- second orthogonality: a nontrivial element sums to zero over the full character group,
-- by reindexing along multiplication by a separating character
private lemma sum_charHom_apply_eq_zero
    {d : G} (hd : d ≠ 1) :
    ∑ χ : G →* Kˣ, ((χ d : Kˣ) : K) = 0 := by
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G K hd
  set S := ∑ χ : G →* Kˣ, ((χ d : Kˣ) : K) with hS
  have hshift : ((ψ d : Kˣ) : K) * S = S := by
    rw [hS, mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft ψ) _ _ fun χ ↦ by simp [Units.val_mul]
  have hzero : (((ψ d : Kˣ) : K) - 1) * S = 0 := by rw [sub_mul, one_mul, hshift, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (by rwa [sub_eq_zero, ← Units.val_one, Units.val_inj] at h) hψ
  · exact h


-- every vector is the sum of its projections, by second orthogonality
private lemma sum_fourierComponent [NeZero (Nat.card G : K)] (v : V) :
    ∑ χ₀ : G →* Kˣ, fourierComponent (ρ := ρ) χ₀ v = v := by
  unfold fourierComponent
  rw [← smul_sum, Finset.sum_comm]
  have hcol : ∀ d : G, ∑ χ₀ : G →* Kˣ, (((χ₀ d)⁻¹ : Kˣ) : K) • ρ d v =
      (∑ χ₀ : G →* Kˣ, ((χ₀ d⁻¹ : Kˣ) : K)) • ρ d v := by
    intro d
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun χ₀ _ ↦ by rw [map_inv]
  rw [Finset.sum_congr rfl fun d _ ↦ hcol d]
  have hsplit : ∀ d : G, d ≠ 1 → (∑ χ₀ : G →* Kˣ, ((χ₀ d⁻¹ : Kˣ) : K)) • ρ d v = 0 := by
    intro d hd
    rw [sum_charHom_apply_eq_zero (by simpa using hd), zero_smul]
  rw [Finset.sum_eq_single 1 (fun d _ hd ↦ hsplit d hd) (by simp)]
  have hone : ∀ χ₀ : G →* Kˣ, ((χ₀ (1 : G)⁻¹ : Kˣ) : K) = 1 := by simp
  rw [Finset.sum_congr rfl fun χ₀ _ ↦ hone χ₀]
  have hcard : (∑ _χ₀ : G →* Kˣ, (1 : K)) = (Nat.card G : K) := by
    rw [Finset.sum_const, card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card,
      card_charHom]
  rw [hcard, map_one, Module.End.one_apply, smul_smul,
    inv_mul_cancel₀ (NeZero.ne _), one_smul]

/-- **Unconditional character-indexed spanning** for a finite commutative group acting on
an arbitrary module over a field with enough roots of unity: the classical character
projectors decompose every vector, with no finite-dimensionality or semisimplicity
hypotheses. -/
@[simp]
theorem iSup_iInf_eigenspace_charHom_eq_top_of_commGroup [NeZero (Nat.card G : K)] :
    (⨆ χ₀ : G →* Kˣ, ⨅ g, (ρ g).eigenspace (χ₀ g)) = ⊤ := by
  refine top_unique fun v _ ↦ ?_
  rw [← sum_fourierComponent (ρ := ρ) v]
  exact Submodule.sum_mem _ fun χ₀ _ ↦ Submodule.mem_iSup_of_mem χ₀
    (Submodule.mem_iInf _ |>.mpr fun g ↦ fourierComponent_mem ρ χ₀ v g)

/-- **Unconditional decomposition of an invariant submodule**: the character projectors
preserve every `ρ`-invariant submodule, so it is the supremum of its intersections with
the joint eigenspaces — again with no finite-dimensionality hypothesis. -/
theorem iSup_inf_iInf_eigenspace_charHom_of_invariant_of_commGroup
    [NeZero (Nat.card G : K)]
    (p : Submodule K V) (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p) :
    (⨆ χ₀ : G →* Kˣ, p ⊓ ⨅ g, (ρ g).eigenspace (χ₀ g)) = p := by
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) fun v hv ↦ ?_
  rw [← sum_fourierComponent (ρ := ρ) v]
  refine Submodule.sum_mem _ fun χ₀ _ ↦ Submodule.mem_iSup_of_mem χ₀ ?_
  refine Submodule.mem_inf.mpr ⟨?_, Submodule.mem_iInf _ |>.mpr fun g ↦
    fourierComponent_mem ρ χ₀ v g⟩
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun d _ ↦
    Submodule.smul_mem _ _ (hp d v hv))

end FourierDecomposition

end
