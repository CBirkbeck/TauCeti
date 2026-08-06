/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
public import TauCeti.NumberTheory.ModularForms.STransform

import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The arc self-pairing of the logarithmic-derivative integrand

The reflection `t ↦ 4 - t` carries the unit-circle arc of the boundary contour to its
own reversal through the inversion `S`. Composed with the `S`-transformation law of the
logarithmic derivative of a weight-`k` form, the reflected integrand
`logDeriv g (γ (4 - t)) · γ' (4 - t)` pairs with the direct one up to the weight term
`-k · γ' / γ` — so the two halves of the arc integral collapse to the integral of
`γ' / γ`, which is the constant `π/6 · i` producing the `k/12` term of the valence
formula.

## Main declarations

* `TauCeti.ModularForm.logDeriv_comp_ofComplex_fdBoundary_arc_pairing`: the direct and
  reflected arc contour integrands sum to the weight term.
* `TauCeti.ModularForm.integral_deriv_div_fdBoundary_arc`: the arc integral of `γ' / γ`
  is `(b - a) · π/6 · i`.
-/

public section

open Complex MeasureTheory Set UpperHalfPlane

open scoped MatrixGroups Real

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- The positivity of the imaginary part along the arc. -/
lemma im_fdBoundary_arc_pos (H : ℝ) {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) :
    0 < (fdBoundary H t).im := by
  rw [eqOn_fdBoundary_arc H ht, circleMap_zero_im, one_mul]
  exact Real.sin_pos_of_pos_of_lt_pi
    (mul_pos (by linarith [ht.1]) (by positivity))
    (by nlinarith [mul_pos Real.pi_pos (show (0 : ℝ) < 5 - t by linarith [ht.2])])

/-- On the open arc, the direct and reflected logarithmic-derivative contour integrands
sum to the weight term `-k · γ' / γ`. -/
theorem logDeriv_comp_ofComplex_fdBoundary_arc_pairing [SlashInvariantFormClass F Γ k]
    (f : F) (hS : ModularGroup.S ∈ Γ) {H t : ℝ} (ht : t ∈ Ioo (1 : ℝ) 3)
    (hd : DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0) :
    deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t) +
      deriv (fdBoundary H) (4 - t) • logDeriv (⇑f ∘ ofComplex) (fdBoundary H (4 - t)) =
      -(k * (deriv (fdBoundary H) t / fdBoundary H t)) := by
  have him := im_fdBoundary_arc_pos H ⟨ht.1.le, ht.2.le⟩
  have h0 : fdBoundary H t ≠ 0 := fun h ↦ absurd him (by simp [h])
  rw [fdBoundary_four_sub_arc H ⟨ht.1.le, ht.2.le⟩, deriv_fdBoundary_four_sub_arc H ht,
    smul_eq_mul, smul_eq_mul, logDeriv_comp_ofComplex_S_transform f hS him hd hne]
  field_simp
  ring

/-- The arc integral of `γ' / γ` over any subinterval of the arc, in either orientation:
the integrand is the constant `π/6 · i`. -/
theorem integral_deriv_div_fdBoundary_arc (H : ℝ) {a b : ℝ} (ha : a ∈ Icc (1 : ℝ) 3)
    (hb : b ∈ Icc (1 : ℝ) 3) :
    ∫ t in a..b, deriv (fdBoundary H) t / fdBoundary H t =
      (b - a) * ((π / 6 : ℝ) * Complex.I) := by
  have key : ∀ c d : ℝ, c ∈ Icc (1 : ℝ) 3 → d ∈ Icc (1 : ℝ) 3 → c ≤ d →
      ∫ t in c..d, deriv (fdBoundary H) t / fdBoundary H t =
        (d - c) * ((π / 6 : ℝ) * Complex.I) := by
    intro c d hc hd hcd
    have hcongr : ∀ t ∈ Ioo c d, deriv (fdBoundary H) t / fdBoundary H t =
        ((π / 6 : ℝ) : ℂ) * Complex.I := fun t ht ↦ by
      have ht' : t ∈ Ioo (1 : ℝ) 3 :=
        ⟨lt_of_le_of_lt hc.1 ht.1, lt_of_lt_of_le ht.2 hd.2⟩
      rw [deriv_fdBoundary_of_mem_Ioo_one_three ht',
        eqOn_fdBoundary_arc H ⟨ht'.1.le, ht'.2.le⟩, Complex.real_smul,
        mul_comm (circleMap 0 1 ((t + 1) * (Real.pi / 6))) Complex.I, mul_div_assoc,
        mul_div_assoc, div_self (circleMap_ne_center one_ne_zero), mul_one]
    rw [intervalIntegral.integral_congr_Ioo_of_le hcd hcongr,
      intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  rcases le_total a b with hab | hab
  · exact key a b ha hb hab
  · rw [intervalIntegral.integral_symm, key b a hb ha hab]
    push_cast
    ring

end ModularForm

end TauCeti

end
