/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import TauCeti.NumberTheory.ModularForms.NormTrace
public import TauCeti.NumberTheory.ModularForms.QExpansionOrder

/-!
# The Sturm bound for finite-index subgroups of `SL(2, ℤ)`

For `𝒢 ≤ GL(2, ℝ)` of finite relative index in `𝒮ℒ` and `f : ModularForm 𝒢 k`, if the
`q`-expansion of `f` at the cusp `∞` (with cusp width `𝒢.strictWidthInfty`) has order
strictly greater than `k · [𝒮ℒ : 𝒢 ⊓ 𝒮ℒ] / 12`, then `f = 0`.

The proof lifts the level-one bound `ModularForm.sturm_bound_levelOne` through the norm map:
the norm of `f` vanishes exactly when `f` does, and by the decomposition
`TauCeti.ModularForm.exists_norm_decomposition` sufficient vanishing of `f` at `∞`
propagates to the norm.

## Main declarations

* `TauCeti.ModularForm.sturm_bound_finiteIndex`: the Sturm bound for finite relative index.
* `TauCeti.ModularForm.sturm_bound_finiteIndex_SL2Z`: the classical form for finite-index
  subgroups of `SL(2, ℤ)`.
* `TauCeti.ModularForm.finiteDimensional_modularForm_finiteIndex`: `ModularForm 𝒢 k` is
  finite-dimensional over `ℂ`.

## References

* [Mathlib PR #39000](https://github.com/leanprover-community/mathlib4/pull/39000)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex Function SlashInvariantForm Periodic Subgroup

open scoped ModularForm Topology Filter Manifold MatrixGroups

namespace TauCeti

namespace ModularForm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ] {k : ℤ} (f : ModularForm 𝒢 k)

private lemma qExpansion_order_le_qExpansion_norm_order [DiscreteTopology 𝒢.strictPeriods] :
    (qExpansion 𝒢.strictWidthInfty f).order ≤
      (qExpansion 1 (_root_.ModularForm.norm 𝒮ℒ f)).order := by
  obtain ⟨m', hm'_pos, hnRw⟩ :=
    Subgroup.exists_pos_nat_integerCuspWidth_eq_mul_strictWidthInfty (𝒢 := 𝒢)
  have hn_pos : 0 < Subgroup.integerCuspWidth 𝒢 := Subgroup.integerCuspWidth_pos
  have hnR_pos : (0 : ℝ) < Subgroup.integerCuspWidth 𝒢 := by exact_mod_cast hn_pos
  have hf_w_per : Function.Periodic (⇑f ∘ ofComplex) 𝒢.strictWidthInfty :=
    SlashInvariantFormClass.periodic_comp_ofComplex f 𝒢.strictWidthInfty_mem_strictPeriods
  have hf_bdd : IsBoundedAtImInfty f := OnePoint.isBoundedAt_infty_iff.mp <|
    f.bdd_at_cusps' <|
      Subgroup.isCusp_of_mem_strictPeriods hnR_pos Subgroup.integerCuspWidth_mem_strictPeriods
  have hf_n_per : Function.Periodic (⇑f ∘ ofComplex)
      ((Subgroup.integerCuspWidth 𝒢 : ℕ) : ℝ) := by
    rw [hnRw]
    exact_mod_cast hf_w_per.nat_mul m'
  obtain ⟨rest, _, h_rest_an, h_decomp⟩ := exists_norm_decomposition f
  rw [show qExpansion 1 (_root_.ModularForm.norm 𝒮ℒ f) =
        qExpansion 1 (galoisProd (Subgroup.integerCuspWidth 𝒢) ⇑f) * qExpansion 1 rest by
      rw [funext h_decomp]
      exact qExpansion_mul (analyticAt_cuspFunction_zero one_pos
        (galoisProd_periodic_one hf_n_per) (mdifferentiable_galoisProd f.holo')
        (isBoundedAtImInfty_galoisProd hf_bdd)) h_rest_an,
    PowerSeries.order_mul,
    qExpansion_one_galoisProd_order_eq hn_pos hf_n_per hf_bdd f.holo']
  refine le_trans ?_ le_self_add
  rw [hnRw]
  exact qExpansion_order_le_qExpansion_nat_mul_order
    (𝒢.strictWidthInfty_nonneg.lt_of_ne fun heq ↦ by
      rw [← heq, mul_zero] at hnRw
      exact hnR_pos.ne' hnRw)
    hm'_pos hf_w_per hf_bdd f.holo'

/-- **Sturm bound for subgroups of `GL(2, ℝ)` of finite relative index in `SL(2, ℤ)`.** A
modular form of weight `k` whose `q`-expansion at the cusp `∞` has order strictly greater
than `k · [𝒮ℒ : 𝒢 ⊓ 𝒮ℒ] / 12` is identically zero. -/
theorem sturm_bound_finiteIndex [DiscreteTopology 𝒢.strictPeriods]
    (h : (↑((k * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)).toNat / 12) : ℕ∞) <
      (qExpansion 𝒢.strictWidthInfty f).order) : f = 0 := by
  rw [← _root_.ModularForm.coe_eq_zero_iff, ← _root_.ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ)]
  exact _root_.ModularForm.sturm_bound_levelOne <|
    h.trans_le (qExpansion_order_le_qExpansion_norm_order f)

/-- **Classical Sturm bound for finite-index subgroups of `SL(2, ℤ)`.** -/
theorem sturm_bound_finiteIndex_SL2Z {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    {k : ℤ} (f : ModularForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (h : (↑((k * Γ.index).toNat / 12) : ℕ∞) <
      (qExpansion (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)).strictWidthInfty f).order) :
    f = 0 := by
  have h_index :
      Nat.card (𝒮ℒ ⧸ (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)).subgroupOf 𝒮ℒ) = Γ.index := by
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex,
      MonoidHom.range_eq_map (Matrix.SpecialLinearGroup.mapGL ℝ), ← Subgroup.relIndex_comap,
      Subgroup.comap_map_eq_self_of_injective Matrix.SpecialLinearGroup.mapGL_injective,
      Subgroup.relIndex_top_right]
  exact sturm_bound_finiteIndex f (h_index ▸ h)

/-- The `ℂ`-linear map sending a weight-`k` modular form for `𝒢` to the vector of the first
`N` coefficients of its `q`-expansion at the cusp `∞` (cusp width `𝒢.strictWidthInfty`). -/
def qExpansionCoeffLinearMap {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] {k : ℤ} (N : ℕ)
    (hh : 0 < 𝒢.strictWidthInfty) (hΓ : 𝒢.strictWidthInfty ∈ 𝒢.strictPeriods) :
    ModularForm 𝒢 k →ₗ[ℂ] (Fin N → ℂ) :=
  LinearMap.pi fun i ↦ (PowerSeries.coeff (i : ℕ)).comp (ModularForm.qExpansionLinearMap hh hΓ k)

/-- **Finite-dimensionality of modular forms.** As a corollary of the Sturm bound, the space
`ModularForm 𝒢 k` is finite-dimensional over `ℂ` for any subgroup `𝒢 ≤ GL(2, ℝ)` of finite
relative index in `𝒮ℒ` with determinant-one elements and discrete strict periods. -/
instance finiteDimensional_modularForm_finiteIndex
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] [𝒢.IsFiniteRelIndex 𝒮ℒ]
    [DiscreteTopology 𝒢.strictPeriods] {k : ℤ} :
    Module.Finite ℂ (ModularForm 𝒢 k) := by
  set N : ℕ := (k * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)).toNat / 12 + 1
  have hh : 0 < 𝒢.strictWidthInfty :=
    𝒢.strictWidthInfty_pos_iff.mpr <| Subgroup.isCusp_of_mem_strictPeriods
      (by exact_mod_cast Subgroup.integerCuspWidth_pos (𝒢 := 𝒢))
      Subgroup.integerCuspWidth_mem_strictPeriods
  have hΓ : 𝒢.strictWidthInfty ∈ 𝒢.strictPeriods := 𝒢.strictWidthInfty_mem_strictPeriods
  refine Module.Finite.of_injective (qExpansionCoeffLinearMap N hh hΓ)
    ((injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_)
  exact sturm_bound_finiteIndex f <| lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) <|
    PowerSeries.nat_le_order _ _ fun i hi ↦ by
      simpa [qExpansionCoeffLinearMap] using congr_fun hf ⟨i, hi⟩

end ModularForm

end TauCeti

end
