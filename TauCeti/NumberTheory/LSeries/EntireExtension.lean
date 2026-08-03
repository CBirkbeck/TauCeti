/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.NumberTheory.LSeries.Convergence

/-!
# The entire-continuation predicate for L-series

The entire-continuation obligation of Hecke theory, as a predicate on a coefficient
sequence `a : ℕ → ℂ`: `LSeries.HasEntireExtension a` says the abscissa of absolute
convergence is finite and some entire function agrees with `LSeries a` on the (nonempty)
convergence half-plane. Such an extension is unique (`LSeries.HasEntireExtension.unique`)
by analytic continuation.

The predicate comes with an introduction lemma (`LSeries.HasEntireExtension.of_extension`)
and elimination lemmas (`.abscissa_lt_top`, `.exists_extension`), so consumers never
unfold the definition. It is exercised: `LSeries.hasEntireExtension_delta` is a
nondegenerate witness, and `LSeries.HasEntireExtension.existsUnique` pins down the unique
extension.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/LFunction.lean`). This is prerequisite infrastructure:
general `LSeries` API with no modular-forms dependence, supplied ahead of the
ModularForms roadmap's Layer-7 entirety/functional-equation obligations, and usable by
any Dirichlet-series development.

## References

* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>
  (`Modularforms/LFunction.lean`)
-/

public section

namespace LSeries

open Filter

/-- **Hecke entire-continuation predicate.** A coefficient sequence `a : ℕ → ℂ` *has an
entire extension* if its abscissa of absolute convergence is finite — so the agreement
region below is a genuine half-plane, not vacuously empty — and some entire `F : ℂ → ℂ`
agrees with `LSeries a` on it. The extension is unique (`HasEntireExtension.unique`). -/
def HasEntireExtension (a : ℕ → ℂ) : Prop :=
  abscissaOfAbsConv a < ⊤ ∧
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s

namespace HasEntireExtension

variable {a : ℕ → ℂ}

/-- Introduction lemma for `HasEntireExtension`: exhibit an entire function agreeing with
`LSeries a` on the absolute-convergence half-plane. -/
theorem of_extension {F : ℂ → ℂ} (h_finite : abscissaOfAbsConv a < ⊤)
    (hF : Differentiable ℂ F)
    (hFa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s) :
    HasEntireExtension a :=
  ⟨h_finite, F, hF, hFa⟩

/-- The abscissa of absolute convergence of a sequence with an entire extension is
finite. -/
theorem abscissa_lt_top (h : HasEntireExtension a) : abscissaOfAbsConv a < ⊤ := h.1

/-- Elimination lemma for `HasEntireExtension`: some entire function agrees with
`LSeries a` on the absolute-convergence half-plane. -/
theorem exists_extension (h : HasEntireExtension a) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s := h.2

/-- **Uniqueness of the entire extension**: two entire functions that both extend
`LSeries a` on the absolute-convergence half-plane are equal everywhere on `ℂ`. -/
theorem unique {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h_finite : abscissaOfAbsConv a < ⊤)
    (hFa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s)
    (hGa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → G s = LSeries a s) :
    F = G := by
  obtain ⟨σ, hσ_abs, -⟩ := EReal.exists_between_coe_real h_finite
  set U : Set ℂ := {s : ℂ | (σ : ℝ) < s.re} with hU_def
  have hU_sub : ∀ s ∈ U, abscissaOfAbsConv a < (s.re : EReal) := fun s hs ↦
    lt_of_lt_of_le hσ_abs (by exact_mod_cast (hs : (σ : ℝ) < s.re).le)
  have hz₀ : ((σ + 1 : ℝ) : ℂ) ∈ U := by
    have h_re : ((σ + 1 : ℝ) : ℂ).re = σ + 1 := Complex.ofReal_re _
    simp only [hU_def, Set.mem_ofPred_eq, h_re]
    linarith
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG)
    (Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨U, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀,
        fun s hs ↦ (hFa (hU_sub s hs)).trans (hGa (hU_sub s hs)).symm⟩)

/-- The entire extension, as an `∃!`: `HasEntireExtension` pins down a unique entire
function agreeing with `LSeries a` on the convergence half-plane. -/
theorem existsUnique (h : HasEntireExtension a) :
    ∃! F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ ⦃s : ℂ⦄, abscissaOfAbsConv a < s.re → F s = LSeries a s := by
  obtain ⟨F, hF, hFa⟩ := h.exists_extension
  refine ⟨F, ⟨hF, fun s hs ↦ hFa hs⟩, fun G ⟨hG, hGa⟩ ↦ ?_⟩
  exact unique hG hF h.abscissa_lt_top (fun {s} hs ↦ hGa hs) (fun {s} hs ↦ hFa hs)

end HasEntireExtension

/-- The delta sequence (the coefficients of the constant Dirichlet series `1`) has an
entire extension, witnessed by the constant function `1`: the predicate is not vacuous. -/
theorem hasEntireExtension_delta : HasEntireExtension LSeries.delta := by
  refine .of_extension (F := fun _ ↦ 1) ?_ (differentiable_const 1) fun {s} _ ↦ ?_
  · refine lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le (s := (2 : ℂ)) ?_) (by simp)
    refine summable_of_ne_finset_zero (s := {1}) fun n hn ↦ ?_
    rw [LSeries.term_delta]
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  · rw [LSeries_delta]
    rfl

end LSeries
