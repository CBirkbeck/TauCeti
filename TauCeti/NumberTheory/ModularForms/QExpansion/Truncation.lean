/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Finitely many `q`-coefficients determine a modular form

A modular form is determined by its whole `q`-expansion. On a finite-dimensional space of forms
it is determined by a *finite* initial segment of it, and this file says so: the kernels
`qKerBelow N` of "the first `N` coefficients" decrease, meet in `⊥`, and therefore — the space
being Artinian — reach `⊥` at some finite `N`, at which point the truncation is injective.

Nothing here proves finite-dimensionality; it is a hypothesis. The point of the statement is the
converse use: a bound on `N` turns a space of forms into a subspace of `ℂ^N`.

## Main results

* `ModularForm.qCoeffTruncation`: the first `N` coefficients, as a `ℂ`-linear map to
  `Fin N → ℂ`, with `qKerBelow` its kernel.
* `ModularForm.qKerBelow_iInf_eq_bot`: the kernels meet in `⊥`.
* `ModularForm.exists_qCoeffTruncation_injective`: on a finite-dimensional space of
  forms, some finite truncation is injective.

## References

Ported from AINTLIB's `LeanModularForms` project
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), commit `6d87d596a537`,
Apache 2.0),
`projects/LeanModularForms/LeanModularForms/Modularforms/DimGenCongLevels/FiniteDimensional.lean`
(`qKerBelow`, `qKerBelow_antitone`, `qKerBelow_iInf_eq_bot`, `exists_qKerBelow_eq_bot`,
`exists_qCoeff_injective`). The truncation is bundled as a linear map here, built from this
repository's `ModularForm.qExpansionLinearMap`, so that `qKerBelow` is a `LinearMap.ker` rather
than a submodule with hand-written closure proofs.
-/

public section

open UpperHalfPlane

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {h : ℝ} {k : ℤ}

/-- **The first `N` `q`-expansion coefficients**, as a `ℂ`-linear map to `Fin N → ℂ`. -/
noncomputable def qCoeffTruncation (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) (N : ℕ) :
    ModularForm Γ k →ₗ[ℂ] (Fin N → ℂ) :=
  LinearMap.pi fun n ↦
    (PowerSeries.coeff (n : ℕ)).comp (TauCeti.ModularForm.qExpansionLinearMap hh hΓ k)

@[simp]
theorem qCoeffTruncation_apply (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (N : ℕ)
    (f : ModularForm Γ k) (n : Fin N) :
    qCoeffTruncation hh hΓ k N f n = (qExpansion h f).coeff (n : ℕ) := by
  simp [qCoeffTruncation]

/-- **The forms whose first `N` `q`-coefficients vanish**: the kernel of the truncation. -/
noncomputable def qKerBelow (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) (N : ℕ) :
    Submodule ℂ (ModularForm Γ k) :=
  LinearMap.ker (qCoeffTruncation hh hΓ k N)

theorem mem_qKerBelow_iff {hh : 0 < h} {hΓ : h ∈ Γ.strictPeriods} {N : ℕ}
    {f : ModularForm Γ k} :
    f ∈ qKerBelow hh hΓ k N ↔ ∀ n < N, (qExpansion h f).coeff n = 0 := by
  simp only [qKerBelow, LinearMap.mem_ker, funext_iff, Pi.zero_apply, qCoeffTruncation_apply]
  exact ⟨fun hf n hn ↦ hf ⟨n, hn⟩, fun hf n ↦ hf n n.2⟩

/-- **Asking for more vanishing coefficients cuts the kernel down.** -/
theorem qKerBelow_antitone (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Antitone (qKerBelow hh hΓ k) := fun _ _ hAB _ hf ↦
  mem_qKerBelow_iff.2 fun n hn ↦ mem_qKerBelow_iff.1 hf n (hn.trans_le hAB)

/-- **The kernels meet in `⊥`**: a form all of whose coefficients vanish is zero. -/
theorem qKerBelow_iInf_eq_bot (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    (⨅ N : ℕ, qKerBelow (Γ := Γ) hh hΓ k N) = ⊥ := by
  refine eq_bot_iff.2 fun f hf ↦ ?_
  refine (Submodule.mem_bot ℂ).2 <|
    (_root_.ModularForm.qExpansion_eq_zero_iff hh hΓ f).1 <| PowerSeries.ext fun n ↦ ?_
  exact mem_qKerBelow_iff.1 (Submodule.mem_iInf _ |>.1 hf (n + 1)) n (Nat.lt_succ_self n)

/-- **The kernel reaches `⊥` at a finite stage**, the space of forms being Artinian. -/
theorem exists_qKerBelow_eq_bot (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    [FiniteDimensional ℂ (ModularForm Γ k)] :
    ∃ N : ℕ, qKerBelow (Γ := Γ) hh hΓ k N = ⊥ := by
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := ℂ) (M := ModularForm Γ k)
    { toFun := fun N ↦ OrderDual.toDual (qKerBelow (Γ := Γ) hh hΓ k N)
      monotone' := fun _ _ hAB ↦ qKerBelow_antitone hh hΓ hAB }
  have hle : ∀ M : ℕ, qKerBelow (Γ := Γ) hh hΓ k N ≤ qKerBelow hh hΓ k M := fun M ↦ by
    by_cases hNM : N ≤ M
    · exact le_of_eq (congrArg OrderDual.ofDual (hN M hNM))
    · exact qKerBelow_antitone hh hΓ (Nat.le_of_not_ge hNM)
  refine ⟨N, ?_⟩
  have hEq : qKerBelow (Γ := Γ) hh hΓ k N = ⨅ M : ℕ, qKerBelow (Γ := Γ) hh hΓ k M :=
    le_antisymm (le_iInf hle) (iInf_le _ N)
  rw [hEq, qKerBelow_iInf_eq_bot (Γ := Γ) (k := k) hh hΓ]

/-- **Finitely many `q`-coefficients determine a modular form**, on a finite-dimensional space
of them: some truncation `f ↦ (a₀ f, …, a_{N-1} f)` is injective. -/
theorem exists_qCoeffTruncation_injective (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    [FiniteDimensional ℂ (ModularForm Γ k)] :
    ∃ N : ℕ, Function.Injective (qCoeffTruncation (Γ := Γ) hh hΓ k N) := by
  obtain ⟨N, hN⟩ := exists_qKerBelow_eq_bot (Γ := Γ) (k := k) hh hΓ
  exact ⟨N, LinearMap.ker_eq_bot.1 hN⟩

end ModularForm
