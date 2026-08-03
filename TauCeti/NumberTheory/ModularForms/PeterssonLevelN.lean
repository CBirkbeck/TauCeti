/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.NumberTheory.ModularForms.PeterssonInner

/-!
# The level-`N` Petersson pairing

The **level-`N` Petersson pairing** on `S_k(Γ₁(N))`, defined as a sum over left coset
representatives of `Γ₁(N)` in `SL₂(ℤ)`:

$$\langle f, g \rangle_N = \sum_{[\delta] \in \mathrm{SL}_2(\mathbb{Z})\,/\,\Gamma_1(N)}
  \int_{\mathcal{D}} \overline{(f|\delta^{-1})(\tau)}\,(g|\delta^{-1})(\tau)\,
  (\mathrm{Im}\,\tau)^k\,d\mu(\tau)$$

Each summand slashes the forms back by a coset representative and pairs them over the
level-one domain `𝒟`; summing over `SL₂(ℤ) ⧸ Γ₁(N)` makes the result independent of the
representatives. (The identification with a genuine integral over a `Γ₁(N)`-fundamental
domain, and positive definiteness, are subsequent steps of the roadmap's Layer 3.)

## Main definitions

* `CuspForm.petN`: the level-`N` Petersson pairing (un-normalized).

## Main results

* `CuspForm.petN_conj_symm`: Hermitian symmetry.
* `CuspForm.petN_add_left`/`petN_add_right`/`petN_smul_right`/`petN_smul_left`:
  sesquilinearity.
* `CuspForm.slash_Gamma1_eq`: the weight-`k` slash action of `γ ∈ Γ₁(N)` on a
  `Γ₁(N)`-cusp form is trivial.
* `CuspForm.integrableOn_petersson_slash`: each summand's integrand is integrable.

The pairing is deliberately not normalized by the index: a positive-definite Hermitian
form suffices downstream, and the normalization constant would pollute every adjoint
computation. Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/PeterssonLevelN.lean`), realizing the level-`N` pairing
milestone of the ModularForms roadmap's Layer 3.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.4
* [Miy] Miyake, *Modular Forms*, §2.5
-/

public section

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

open UpperHalfPlane ModularGroup CongruenceSubgroup MeasureTheory Matrix.SpecialLinearGroup

namespace CuspForm

variable {N : ℕ} [NeZero N] {k : ℤ}

instance : Fintype (SL(2, ℤ) ⧸ Gamma1 N) := Subgroup.fintypeQuotientOfFiniteIndex

omit [NeZero N] in
/-- For `γ ∈ Γ₁(N)`, the weight-`k` slash action on a `Γ₁(N)`-cusp form is trivial. -/
theorem slash_Gamma1_eq (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    ⇑f ∣[k] γ = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩

/-- The level-`N` Petersson pairing on `S_k(Γ₁(N))`:
`petN f g = Σ_{[δ] ∈ SL₂(ℤ)/Γ₁(N)} ∫ τ in 𝒟, petersson k (f∣δ⁻¹) (g∣δ⁻¹) τ`. -/
def petN (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : ℂ :=
  ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
    UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹)

theorem petN_def (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f g = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹) := (rfl)

/-- Hermitian symmetry: `conj (petN g f) = petN f g`. -/
theorem petN_conj_symm (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    starRingEnd ℂ (petN g f) = petN f g := by
  simp only [petN_def, map_sum, UpperHalfPlane.peterssonInner_conj_symm]

/-- The pairing with zero on the right vanishes. -/
theorem petN_zero_right (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f 0 = 0 := by
  simp [petN_def, ModularForm.SL_slash, SlashAction.zero_slash,
    UpperHalfPlane.peterssonInner_zero_right]

/-- The pairing with zero on the left vanishes. -/
theorem petN_zero_left (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN 0 g = 0 := by
  simp [petN_def, ModularForm.SL_slash, SlashAction.zero_slash,
    UpperHalfPlane.peterssonInner_zero_left]

/-- The Petersson integrand of slashed cusp forms is integrable on `𝒟`. -/
theorem integrableOn_petersson_slash {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    [CuspFormClass F Γ k] [ModularFormClass F' Γ k]
    (f : F) (f' : F') (δ : SL(2, ℤ)) :
    IntegrableOn (fun τ ↦ petersson k (⇑f ∣[k] δ) (⇑f' ∣[k] δ) τ) fd (volume : Measure ℍ) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ f f'
  have h_eq : (fun τ ↦ petersson k (⇑f ∣[k] δ) (⇑f' ∣[k] δ) τ) =
      fun τ ↦ petersson k (⇑f) (⇑f') (δ • τ) :=
    funext fun τ ↦ petersson_slash_SL k _ _ δ τ
  rw [h_eq]
  have h_cont : Continuous fun τ : ℍ ↦ δ • τ := by
    change Continuous fun τ : ℍ ↦ (mapGL ℝ δ) • τ
    exact continuous_const_smul _
  exact IntegrableOn.of_bound ModularGroup.volume_fd_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f')).comp h_cont
    |>.aestronglyMeasurable.restrict)
    C (ae_of_all _ fun τ ↦ hC (δ • τ))

/-- Negation in the second argument. -/
theorem petN_neg_right (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (-g) = -petN f g := by
  simp only [petN_def, coe_neg, ModularForm.SL_slash, SlashAction.neg_slash,
    UpperHalfPlane.peterssonInner_neg_right, Finset.sum_neg_distrib]

/-- Negation in the first argument. -/
theorem petN_neg_left (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (-f) g = -petN f g := by
  simp only [petN_def, coe_neg, ModularForm.SL_slash, SlashAction.neg_slash,
    UpperHalfPlane.peterssonInner_neg_left, Finset.sum_neg_distrib]

/-- Additivity in the second argument. -/
theorem petN_add_right (f g₁ g₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (g₁ + g₂) = petN f g₁ + petN f g₂ := by
  simp only [petN_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have h_slash : ⇑(g₁ + g₂) ∣[k] (q.out)⁻¹ =
      (⇑g₁ ∣[k] (q.out)⁻¹) + (⇑g₂ ∣[k] (q.out)⁻¹) := by
    rw [coe_add]
    exact SlashAction.add_slash k _ _ _
  rw [h_slash]
  exact UpperHalfPlane.peterssonInner_add_right k fd _ _ _
    (integrableOn_petersson_slash f g₁ (q.out)⁻¹)
    (integrableOn_petersson_slash f g₂ (q.out)⁻¹)

private lemma smul_slash_SL (c : ℂ) (f : ℍ → ℂ) (δ : SL(2, ℤ)) :
    (c • f) ∣[k] δ = c • (f ∣[k] δ) := by
  rw [ModularForm.SL_slash (c • f) δ, ModularForm.SL_slash f δ, ModularForm.smul_slash]
  simp [UpperHalfPlane.σ, Matrix.SpecialLinearGroup.map]

/-- Complex scalar in the second argument: `petN f (c • g) = c * petN f g`. -/
theorem petN_smul_right (c : ℂ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (c • g) = c * petN f g := by
  simp only [petN_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have h_slash : ⇑(c • g) ∣[k] (q.out)⁻¹ = c • (⇑g ∣[k] (q.out)⁻¹) := by
    rw [IsGLPos.coe_smul]
    exact smul_slash_SL c _ _
  rw [h_slash]
  exact UpperHalfPlane.peterssonInner_smul_right k _ c _ _

/-- Conjugate-complex scalar in the first argument:
`petN (c • f) g = conj c * petN f g`. -/
theorem petN_smul_left (c : ℂ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (c • f) g = starRingEnd ℂ c * petN f g :=
  calc petN (c • f) g
      = starRingEnd ℂ (petN g (c • f)) := (petN_conj_symm _ _).symm
    _ = starRingEnd ℂ (c * petN g f) := by rw [petN_smul_right]
    _ = starRingEnd ℂ c * starRingEnd ℂ (petN g f) := map_mul _ _ _
    _ = starRingEnd ℂ c * petN f g := by rw [petN_conj_symm]

/-- Additivity in the first argument. -/
theorem petN_add_left (f₁ f₂ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (f₁ + f₂) g = petN f₁ g + petN f₂ g :=
  calc petN (f₁ + f₂) g
      = starRingEnd ℂ (petN g (f₁ + f₂)) := (petN_conj_symm _ _).symm
    _ = starRingEnd ℂ (petN g f₁ + petN g f₂) := by rw [petN_add_right]
    _ = starRingEnd ℂ (petN g f₁) + starRingEnd ℂ (petN g f₂) := map_add _ _ _
    _ = petN f₁ g + petN f₂ g := by rw [petN_conj_symm, petN_conj_symm]

end CuspForm
