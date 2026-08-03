/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction
public import TauCeti.NumberTheory.ModularForms.PeterssonInner

/-!
# `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)`

The open modular domain `𝒟ᵒ = ModularGroup.fdo` is a `MeasureTheory.IsFundamentalDomain`
for the `PSL(2, ℤ)`-action on `ℍ` with the invariant measure: its translates cover `ℍ` up
to the null boundary `𝒟 \ 𝒟ᵒ` (`ModularGroup.exists_smul_mem_fd` +
`ModularGroup.volume_frontier_fd`), and distinct `PSL(2, ℤ)`-translates are *genuinely*
disjoint — on the projective group the `±I` ambiguity of
`ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo` disappears.

## Main results

* `ModularGroup.isFundamentalDomain_fdo_PSL`: `𝒟ᵒ` is a `PSL(2, ℤ)`-fundamental domain for
  `(ℍ, volume)`.

This is the "measurable fundamental domain" milestone of the ModularForms roadmap's
Layer 3 at level one; fundamental domains for finite-index subgroups follow by coset
tiling in a separate file. Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/PSL2Action.lean`).
-/

public section

noncomputable section

open scoped MatrixGroups Pointwise

open UpperHalfPlane MeasureTheory Matrix.SpecialLinearGroup

namespace ModularGroup

private theorem mem_center_of_smul_id (g : SL(2, ℤ))
    (htriv : ∀ z : ℍ, g • z = z)
    (hc : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    g ∈ Subgroup.center SL(2, ℤ) := by
  have hdet : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
      (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
  set z₀ : ℍ := ⟨⟨0, 2⟩, by norm_num⟩ with z₀_def
  have z₀_fdo : z₀ ∈ fdo := by
    constructor
    · norm_num [z₀_def, Complex.normSq_apply]
    · norm_num [z₀_def]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · have hg : g = T ^ ((↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
      ext i j
      simp only [coe_T_zpow]
      fin_cases i <;> fin_cases j <;> simp_all
    have hb := eq_zero_of_mem_fdo_of_T_zpow_mem_fdo z₀_fdo (hg ▸ htriv z₀ ▸ z₀_fdo)
    rw [hg, hb, zpow_zero]
    exact one_mem _
  · have hng : -g = T ^ (-((↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 1)) := by
      ext i j
      simp only [coe_T_zpow, coe_neg]
      fin_cases i <;> fin_cases j <;> simp_all
    have hb : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by
      have h2 : (-g) • z₀ = z₀ := by
        rw [SL_neg_smul]
        exact htriv z₀
      rw [hng] at h2
      have h0 := eq_zero_of_mem_fdo_of_T_zpow_mem_fdo z₀_fdo (h2 ▸ z₀_fdo)
      lia
    have hg_neg : g = -1 := neg_eq_iff_eq_neg.mp (by rw [hng, hb, neg_zero, zpow_zero])
    rw [hg_neg]
    refine Subgroup.mem_center_iff.mpr fun x ↦ ?_
    ext i j
    simp [coe_neg, neg_mul, mul_neg]

private theorem pairwise_disjoint_smul_fdo :
    Pairwise fun (g₁ g₂ : PSL(2, ℤ)) ↦ Disjoint (g₁ • (fdo : Set ℍ)) (g₂ • fdo) := by
  intro g₁ g₂ hne
  rw [Set.disjoint_left]
  intro τ h1 h2
  obtain ⟨σ₁, hσ₁, rfl⟩ := h1
  obtain ⟨σ₂, hσ₂, h_eq⟩ := h2
  induction g₁ using Quotient.inductionOn with | h a => ?_
  induction g₂ using Quotient.inductionOn with | h b => ?_
  simp only [PSL_smul_coe] at h_eq
  have hba : (b⁻¹ * a) • σ₁ = σ₂ := by rw [mul_smul, ← h_eq, inv_smul_smul]
  refine hne ?_
  have hc : ((b⁻¹ * a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hσ₁ (hba ▸ hσ₂) with h | h <;> rw [h] <;> rfl
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
  have hn0 := eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hσ₁ (hn σ₁ ▸ (hba ▸ hσ₂))
  have htriv : ∀ z : ℍ, (b⁻¹ * a) • z = z := fun z ↦ by
    rw [hn z, hn0, zpow_zero, one_smul]
  have h_inv : a⁻¹ * b = (b⁻¹ * a)⁻¹ := by group
  rw [Quotient.eq, QuotientGroup.leftRel_apply, h_inv]
  exact (Subgroup.center _).inv_mem (mem_center_of_smul_id _ htriv hc)

/-- **The open modular domain `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)`** acting on
`ℍ` with the invariant measure: a.e. every point moves into `𝒟ᵒ` (the missed points land
on the null boundary `𝒟 \ 𝒟ᵒ`), and distinct `PSL(2, ℤ)`-translates of `𝒟ᵒ` are
disjoint — projectivizing removes the `±I` ambiguity of the `SL(2, ℤ)`-action. -/
theorem isFundamentalDomain_fdo_PSL :
    IsFundamentalDomain PSL(2, ℤ) (fdo : Set ℍ) (volume : Measure ℍ) where
  nullMeasurableSet := isOpen_fdo.measurableSet.nullMeasurableSet
  ae_covers := by
    have h_null : (volume : Measure ℍ) (fd \ fdo : Set ℍ) = 0 := by
      have h := volume_frontier_fd
      rwa [frontier, isClosed_fd.closure_eq, ← fdo_eq_interior_fd] at h
    have h_subset : {x | ¬∃ g : PSL(2, ℤ), g • x ∈ fdo} ⊆
        ⋃ g : SL(2, ℤ), (g • ·) ⁻¹' (fd \ fdo) := by
      intro τ hτ
      push Not at hτ
      obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
      exact Set.mem_iUnion.mpr ⟨g, Set.mem_preimage.mpr ⟨hg, PSL_smul_coe g τ ▸ hτ ↑g⟩⟩
    rw [ae_iff]
    apply measure_mono_null h_subset
    refine measure_iUnion_null fun g ↦ ?_
    rw [(measurePreserving_smul g (volume : Measure ℍ)).measure_preimage
      ((isClosed_fd.measurableSet.diff isOpen_fdo.measurableSet).nullMeasurableSet)]
    exact h_null
  aedisjoint _ _ hne := (pairwise_disjoint_smul_fdo hne).aedisjoint

end ModularGroup
