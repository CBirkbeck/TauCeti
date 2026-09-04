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

## Main results

* `TauCeti.exists_slash_T_invariant_of_qExpansionSupportedOnDvd`: the descent.

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

variable {N l : ℕ} [NeZero l] {k : ℤ}

/-- Slashing by `T` translates the argument by one. -/
private lemma slash_mapGL_T_apply (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ)) τ = f ((1 : ℝ) +ᵥ τ) := by
  have hSL : (f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ)) =
      f ∣[k] (ModularGroup.T : SL(2, ℤ)) :=
    (ModularForm.SL_slash (f := f) (k := k) ModularGroup.T).symm
  rw [hSL, ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul]
  simp [UpperHalfPlane.denom, ModularGroup.coe_T]

/-- Scaling down commutes with translation, at the cost of dividing the shift by `l`. -/
private lemma inv_scaleGL_smul_vadd_one (τ : ℍ) :
    ((scaleGL l)⁻¹ • ((1 : ℝ) +ᵥ τ) : ℍ) = ((1 : ℝ) / (l : ℝ)) +ᵥ ((scaleGL l)⁻¹ • τ) := by
  have hl : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  have h : ∀ σ : ℍ, (((scaleGL l)⁻¹ • σ : ℍ) : ℂ) = (σ : ℂ) / (l : ℂ) := fun σ ↦ by
    have hs := coe_scaleGL_smul (d := l) ((scaleGL l)⁻¹ • σ)
    rw [smul_inv_smul] at hs
    rw [hs, mul_comm, mul_div_assoc, div_self hl, mul_one]
  apply UpperHalfPlane.ext
  rw [h ((1 : ℝ) +ᵥ τ), UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd, h τ]
  push_cast
  ring

/-- Translating by `1 / l` fixes every `q`-power the support condition leaves alive: it scales
the `n`-th by an `l`-th root of unity to the `n`, trivial exactly when `l ∣ n`. -/
private lemma smul_qParam_pow_shift_eq {c : ℕ → ℂ} (hc : ∀ n : ℕ, ¬ l ∣ n → c n = 0)
    (σ : ℍ) (n : ℕ) :
    c n • Function.Periodic.qParam (1 : ℝ) ((((1 : ℝ) / (l : ℝ)) +ᵥ σ : ℍ) : ℂ) ^ n =
      c n • Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n := by
  have hqP : Function.Periodic.qParam (1 : ℝ) ((((1 : ℝ) / (l : ℝ)) +ᵥ σ : ℍ) : ℂ) =
      Function.Periodic.qParam (1 : ℝ) (σ : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) := by
    simp only [Function.Periodic.qParam, UpperHalfPlane.coe_vadd, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  by_cases hln : l ∣ n
  · obtain ⟨m, rfl⟩ := hln
    rw [hqP, mul_pow, pow_mul (Complex.exp _) l m,
      (Complex.isPrimitiveRoot_exp l (NeZero.ne l)).pow_eq_one, one_pow, mul_one]
  · rw [hc n hln, zero_smul, zero_smul]

/-- The scaled-down form is `T`-invariant, by uniqueness of the `q`-expansion sum. -/
private lemma slash_T_eq_of_support (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ¬ l ∣ n → (qExpansion 1 g).coeff n = 0) :
    (fun τ ↦ (⇑g : ℍ → ℂ) ((scaleGL l)⁻¹ • τ)) ∣[k]
        (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) =
      fun τ ↦ (⇑g : ℍ → ℂ) ((scaleGL l)⁻¹ • τ) := by
  funext τ
  rw [slash_mapGL_T_apply, inv_scaleGL_smul_vadd_one]
  set σ : ℍ := (scaleGL l)⁻¹ • τ
  have h1 := one_mem_strictPeriods_Gamma1_map N
  have : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
    ⟨((Gamma1 N).map (mapGL ℝ)).isCusp_of_mem_strictPeriods one_pos h1⟩
  have key := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex g h1) (ModularFormClass.holo g)
    (ModularFormClass.bdd_at_infty g)
  have Hσ' := key (((1 : ℝ) / (l : ℝ)) +ᵥ σ)
  rw [funext (smul_qParam_pow_shift_eq hg σ)] at Hσ'
  exact ((key σ).unique Hσ').symm

/-- **Descent along a `q`-support condition.** A cusp form of level `Γ₁(N)` whose period-one
`q`-expansion is supported on the multiples of `l` is the renormalised slash by `diag(l, 1)` of a
function invariant under the weight-`k` slash action of `T`. -/
theorem exists_slash_T_invariant_of_qExpansionSupportedOnDvd
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : QExpansionSupportedOnDvd l g) :
    ∃ f : ℍ → ℂ, (⇑g : ℍ → ℂ) = (l : ℂ) ^ (1 - k) • (f ∣[k] scaleGL l) ∧
      f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f := by
  refine ⟨fun τ ↦ (⇑g : ℍ → ℂ) ((scaleGL l)⁻¹ • τ), ?_,
    slash_T_eq_of_support g (PowerSeries.isSupportedOnDvd_iff.1
      (qExpansionSupportedOnDvd_iff.1 hg))⟩
  rw [smul_slash_scaleGL_eq]
  funext τ
  rw [inv_smul_smul]

end TauCeti

end
