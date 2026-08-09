/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Assembly

/-!
# The excised boundary contour integral of a level-one logarithmic derivative

`TauCeti.ModularForm.intervalIntegral_logDeriv_fdBoundary` assembles the boundary integral
for a form with no zeros on the contour. The valence formula needs the version that
tolerates them: the elliptic points `i` and `ρ` sit *on* the fundamental-domain boundary, so
a form vanishing there makes `logDeriv f` blow up on the contour itself and the integral only
exists as a principal value. The device is `ε`-excision — the integrand is replaced by `0`
within `ε` of any excision centre — and the excised assembly is what survives.

The three pieces are already available and each already tolerates the excision: the verticals
cancel by periodicity (`intervalIntegral_excised_fdBoundary_segment4_eq_neg_segment1`), the
arc collapses to its weight term
(`two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc`), and
the ceiling is untouched by the excision altogether: the excision centres lie on the unit
circle while the ceiling runs at height `H`, so no ceiling point is within `ε` of one once
`ε < H - 1`.

## Main declarations

* `TauCeti.ModularForm.intervalIntegral_excised_logDeriv_fdBoundary`: the assembled excised
  boundary integral, `2πi · ord_∞ - (k/2) · ∫₁³ (excised logDeriv γ)`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Assembly.lean`) this file ports onto the
  current Mathlib pin.
-/

public section

open Complex Set intervalIntegral UpperHalfPlane

namespace TauCeti

namespace ModularForm

variable {F : Type*} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} {k : ℤ}

/-- **The excision never fires on the ceiling.** The excision centres lie on the unit circle,
so their heights are at most `1`, while the ceiling runs at height `H`; once `ε < H - 1` no
ceiling point is within `ε` of a centre. -/
theorem not_exists_dist_le_of_mem_Icc_four_five {H ε : ℝ} {S : Finset ℂ}
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hε : ε < H - 1) {t : ℝ} (ht : t ∈ Icc (4 : ℝ) 5) :
    ¬ ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε := by
  rintro ⟨s, hs, hle⟩
  have hsim : |s.im| ≤ 1 := (Complex.abs_im_le_norm s).trans (hnorm s hs).le
  have himle : |(fdBoundary H t - s).im| ≤ ‖fdBoundary H t - s‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, im_fdBoundary_segment5 H ht] at himle
  have : H - s.im ≤ ε := (le_abs_self _).trans (himle.trans hle)
  cases abs_le.mp hsim
  linarith

/-- The excision commutes with the scalar multiplication by `deriv γ`: excising the whole
integrand is excising the function it is built from. -/
private lemma excised_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H ε : ℝ}
    {S : Finset ℂ} {φ : ℂ → E} (t : ℝ) :
    (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • φ (fdBoundary H t)) =
    deriv (fdBoundary H) t •
      (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0 else φ (fdBoundary H t)) := by
  split <;> simp

end ModularForm

end TauCeti
