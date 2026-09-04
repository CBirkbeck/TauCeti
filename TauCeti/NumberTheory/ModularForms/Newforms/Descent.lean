/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.QSupport

import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Descent along a `q`-support condition

A cusp form of level `Γ₁(N)` whose period-one `q`-expansion is supported on the multiples of `l`
is `τ ↦ f (l τ)` for a function `f` invariant under the weight-`k` slash action of `T`.

This is the converse half of the Atkin–Lehner description of the old subspace: `QSupport.lean`
shows that a level-raise is `q`-supported on multiples of `l`, and this file recovers a
preimage from that support condition alone. The preimage is only a function — its invariance
under all of `Γ₁(N/l)` is what the conductor dichotomy goes on to establish — so the statement
is about `ℍ → ℂ`, and `Degeneracy.smul_slash_scaleGL_eq` is what phrases `τ ↦ f (l τ)` as the
renormalised slash `l ^ (1 - k) • (f ∣[k] diag(l, 1))` that `levelRaise` uses.

Invariance under `T` is where the support condition is spent: translating by `1 / l` multiplies
the `n`-th `q`-power by a primitive `l`-th root of unity raised to `n`, which is `1` exactly on
the multiples of `l`, and those are the only indices carrying a nonzero coefficient.

Neither the cusp condition nor the congruence level is used. What the argument needs of the group
is that `1` be a strict period — the hypothesis making `qExpansion 1` the right expansion and `∞`
a cusp — so the theorem is stated at an arbitrary `𝒢` carrying that, in the idiom
`Degeneracy.lean` already uses for its `q`-expansion results, and `Γ₁(N)` enters only in the
cusp-form specialisation, through `TauCeti.one_mem_strictPeriods_Gamma1_map`.

## Main results

* `TauCeti.exists_slash_T_invariant_of_isSupportedOnDvd`: the descent, at any group with strict
  period `1`.
* `CuspForm.exists_slash_T_invariant_of_qExpansionSupportedOnDvd`: its `Γ₁(N)` specialisation to
  cusp forms, in the shape the Atkin–Lehner old-subspace argument consumes.

## Provenance

Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Chris Birkbeck, Apache-2.0) at
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Newforms.lean` — the theorem
`exists_levelRaise_preimage_of_coeff_support_multiples` and its three private helpers. The
source's `levelRaiseMatrix l` is this repository's `scaleGL l` and its `levelRaiseFun l k f` is
`l ^ (1 - k) • (f ∣[k] scaleGL l)`, so neither is ported again. The source's `1 < l` and `l ∣ N`
hypotheses are dropped: neither is used, as the underscores on them record.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.6.
* [Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup ModularForm

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {l : ℕ} [NeZero l] {k : ℤ} {𝒢 : Subgroup (GL (Fin 2) ℝ)}

/-- The scaled-down form is `T`-invariant, by uniqueness of the `q`-expansion sum. -/
private lemma slash_T_eq_of_support {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒢 k]
    (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods) (g : F)
    (hg : ∀ n : ℕ, ¬ l ∣ n → (qExpansion 1 g).coeff n = 0) :
    (fun τ ↦ (⇑g : ℍ → ℂ) ((scaleGL l)⁻¹ • τ)) ∣[k]
        (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) =
      fun τ ↦ (⇑g : ℍ → ℂ) ((scaleGL l)⁻¹ • τ) := by
  funext τ
  rw [show (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) =
      ((ModularGroup.T ^ (1 : ℤ) : SL(2, ℤ)) : GL (Fin 2) ℝ) by
        rw [zpow_one, Matrix.SpecialLinearGroup.coe_GL_eq_mapGL],
    ← ModularForm.SL_slash, ModularForm.slash_T_zpow_apply]
  rw [show ((1 : ℤ) : ℝ) = (1 : ℝ) from Int.cast_one, inv_scaleGL_smul_vadd]
  set σ : ℍ := (scaleGL l)⁻¹ • τ
  have : Fact (IsCusp OnePoint.infty 𝒢) := ⟨𝒢.isCusp_of_mem_strictPeriods one_pos h𝒢⟩
  have key := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex g h𝒢) (ModularFormClass.holo g)
    (ModularFormClass.bdd_at_infty g)
  have Hσ' := key (((1 : ℝ) / (l : ℝ)) +ᵥ σ)
  rw [funext (smul_qParam_pow_shift_eq hg σ)] at Hσ'
  exact ((key σ).unique Hσ').symm

/-- **Descent along a `q`-support condition.** A modular form whose period-one `q`-expansion is
supported on the multiples of `l` is the renormalised slash by `diag(l, 1)` of a function
invariant under the weight-`k` slash action of `T`.

Neither a cusp condition nor a congruence level enters. The argument needs only holomorphy,
boundedness at infinity, and that `1` be a strict period of the group — the hypothesis that makes
`qExpansion 1` the right expansion and `∞` a cusp — so it is stated for any `ModularFormClass` at
any such `𝒢`. `TauCeti.one_mem_strictPeriods_Gamma1_map` discharges it at `Γ₁(N)`. -/
theorem exists_slash_T_invariant_of_isSupportedOnDvd {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F 𝒢 k] (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods) (g : F)
    (hg : PowerSeries.IsSupportedOnDvd l (qExpansion 1 g)) :
    ∃ f : ℍ → ℂ, (⇑g : ℍ → ℂ) = (l : ℂ) ^ (1 - k) • (f ∣[k] scaleGL l) ∧
      f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f := by
  refine ⟨fun τ ↦ (⇑g : ℍ → ℂ) ((scaleGL l)⁻¹ • τ), ?_,
    slash_T_eq_of_support h𝒢 g (PowerSeries.isSupportedOnDvd_iff.1 hg)⟩
  rw [smul_slash_scaleGL_eq]
  funext τ
  rw [inv_smul_smul]

end TauCeti

namespace CuspForm

open TauCeti UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup

variable {N l : ℕ} [NeZero l] {k : ℤ}

/-- **Descent along a `q`-support condition, for cusp forms.** The specialisation of
`TauCeti.exists_slash_T_invariant_of_isSupportedOnDvd` at a `CuspForm` and this repository's
`QExpansionSupportedOnDvd`, which is the shape the Atkin–Lehner old-subspace argument consumes.
-/
theorem exists_slash_T_invariant_of_qExpansionSupportedOnDvd
    (g : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : QExpansionSupportedOnDvd l g) :
    ∃ f : ℍ → ℂ, (⇑g : ℍ → ℂ) = (l : ℂ) ^ (1 - k) • (f ∣[k] scaleGL l) ∧
      f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f :=
  exists_slash_T_invariant_of_isSupportedOnDvd (one_mem_strictPeriods_Gamma1_map N) g
    (qExpansionSupportedOnDvd_iff.1 hg)

end CuspForm

end
