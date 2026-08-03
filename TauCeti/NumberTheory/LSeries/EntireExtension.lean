/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.Convergence

/-!
# Analytic continuation predicates for L-series

The two analytic-continuation obligations of Hecke theory, as predicates on a coefficient
sequence `a : ℕ → ℂ`:

* `LSeries.HasEntireExtension a`: the abscissa of absolute convergence is finite and some
  entire function agrees with `LSeries a` on the (nonempty) convergence half-plane. Such
  an extension is unique (`LSeries.HasEntireExtension.unique`) by analytic continuation.
* `LSeries.HasMeromorphicExtensionWithPole a`: the abscissa is finite and a globally
  meromorphic witness agrees with `LSeries a` on the convergence half-plane while having
  a genuine pole (negative meromorphic order) somewhere — the obligation shape ruling out
  entirety, e.g. for Eisenstein L-functions.

Both predicates come with introduction lemmas (`LSeries.HasEntireExtension.of_extension`,
`LSeries.HasMeromorphicExtensionWithPole.of_witness`) and elimination lemmas
(`.abscissa_lt_top`, `.exists_extension`, `.exists_witness`), so consumers never unfold
the definitions. They are exercised: `LSeries.hasEntireExtension_delta` is a
nondegenerate witness, `LSeries.HasEntireExtension.existsUnique` pins down the unique
extension, and `LSeries.HasMeromorphicExtensionWithPole.not_hasEntireExtension` shows the
two obligations exclude each other (via the clopen infinite-order locus of the
meromorphic difference).

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
  · refine lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le (s := 2) ?_) (by simp)
    refine summable_of_ne_finset_zero (s := {1}) fun n hn ↦ ?_
    rw [LSeries.term_delta]
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  · rw [LSeries_delta]
    rfl

/-- **Meromorphic extension with a pole.** A coefficient sequence `a : ℕ → ℂ` (with
finite abscissa of absolute convergence, so the agreement clause is not vacuous) *has a
meromorphic extension with a pole* if some `g : ℂ → ℂ`, meromorphic at every point of
`ℂ`, agrees with `LSeries a` on the absolute-convergence half-plane and has a genuine
pole (negative meromorphic order) at some `s₀`. This is the obligation shape ruling out
an entire extension: an entire extension would agree with `g` on the half-plane, hence —
by analytic continuation off the polar set — near `s₀`, where `g` blows up. -/
def HasMeromorphicExtensionWithPole (a : ℕ → ℂ) : Prop :=
  abscissaOfAbsConv a < ⊤ ∧
    ∃ (g : ℂ → ℂ) (s₀ : ℂ),
      (∀ z : ℂ, MeromorphicAt g z) ∧
      meromorphicOrderAt g s₀ < 0 ∧
      ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → g s = LSeries a s

namespace HasMeromorphicExtensionWithPole

variable {a : ℕ → ℂ}

/-- Introduction lemma for `HasMeromorphicExtensionWithPole`: exhibit a globally
meromorphic function agreeing with `LSeries a` on the absolute-convergence half-plane and
having a pole at `s₀`. -/
theorem of_witness {g : ℂ → ℂ} {s₀ : ℂ} (h_finite : abscissaOfAbsConv a < ⊤)
    (hg : ∀ z : ℂ, MeromorphicAt g z) (h_pole : meromorphicOrderAt g s₀ < 0)
    (h_agree : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → g s = LSeries a s) :
    HasMeromorphicExtensionWithPole a :=
  ⟨h_finite, g, s₀, hg, h_pole, h_agree⟩

/-- The abscissa of absolute convergence of a sequence with a polar meromorphic extension
is finite. -/
theorem abscissa_lt_top (h : HasMeromorphicExtensionWithPole a) :
    abscissaOfAbsConv a < ⊤ := h.1

/-- Elimination lemma for `HasMeromorphicExtensionWithPole`: some globally meromorphic
function agrees with `LSeries a` on the absolute-convergence half-plane and has a pole. -/
theorem exists_witness (h : HasMeromorphicExtensionWithPole a) :
    ∃ (g : ℂ → ℂ) (s₀ : ℂ),
      (∀ z : ℂ, MeromorphicAt g z) ∧
      meromorphicOrderAt g s₀ < 0 ∧
      ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → g s = LSeries a s := h.2

end HasMeromorphicExtensionWithPole

/-- **A meromorphic extension with a pole excludes an entire extension.** The two would
agree on the convergence half-plane; the difference is meromorphic on all of `ℂ` with
infinite order there, so — the infinite-order locus being clopen and `ℂ` preconnected —
they agree near the pole `s₀`, where the meromorphic witness has negative order but an
entire function has nonnegative order. -/
theorem HasMeromorphicExtensionWithPole.not_hasEntireExtension {a : ℕ → ℂ}
    (hm : HasMeromorphicExtensionWithPole a) : ¬ HasEntireExtension a := by
  intro he
  obtain ⟨F, hF, hFa⟩ := he.exists_extension
  obtain ⟨g, s₀, hg_mero, hg_pole, hg_agree⟩ := hm.exists_witness
  set d : ℂ → ℂ := fun z ↦ g z - F z with hd_def
  have hd_mero : MeromorphicOn d Set.univ := fun z _ ↦
    (hg_mero z).sub (hF.analyticAt z).meromorphicAt
  obtain ⟨σ, hσ_abs, -⟩ := EReal.exists_between_coe_real he.abscissa_lt_top
  have h_zero : ∀ z : ℂ, (σ : ℝ) < z.re → d z = 0 := fun z hz ↦ by
    have habs : abscissaOfAbsConv a < (z.re : EReal) :=
      lt_of_lt_of_le hσ_abs (by exact_mod_cast hz.le)
    simp [hd_def, hg_agree habs, hFa habs]
  have h_top : meromorphicOrderAt d ((σ + 1 : ℝ) : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have h_lt : (σ : ℝ) < ((σ + 1 : ℝ) : ℂ).re := by
      rw [Complex.ofReal_re]
      linarith
    have h_mem : ∀ᶠ z in nhds (((σ + 1 : ℝ) : ℂ)), (σ : ℝ) < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).eventually_mem h_lt
    filter_upwards [nhdsWithin_le_nhds h_mem] with z hz
    exact h_zero z hz
  have : PreconnectedSpace (Set.univ : Set ℂ) := Subtype.preconnectedSpace isPreconnected_univ
  have h_univ := (hd_mero.isClopen_setOfPred_meromorphicOrderAt_eq_top).eq_univ
    ⟨⟨((σ + 1 : ℝ) : ℂ), trivial⟩, h_top⟩
  have h_s₀ : meromorphicOrderAt d s₀ = ⊤ :=
    Set.eq_univ_iff_forall.mp h_univ ⟨s₀, trivial⟩
  have h_eq : g =ᶠ[nhdsWithin s₀ {s₀}ᶜ] F := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp h_s₀] with z hz
    exact sub_eq_zero.mp hz
  have h_ord : meromorphicOrderAt g s₀ = meromorphicOrderAt F s₀ :=
    meromorphicOrderAt_congr h_eq
  have h_nonneg : 0 ≤ meromorphicOrderAt F s₀ := (hF.analyticAt s₀).meromorphicOrderAt_nonneg
  rw [h_ord] at hg_pole
  exact absurd h_nonneg (not_le.mpr hg_pole)

end LSeries
