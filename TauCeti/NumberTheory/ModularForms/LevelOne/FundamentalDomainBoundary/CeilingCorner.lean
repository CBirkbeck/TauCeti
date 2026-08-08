/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.InvSubCPVExistence
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Immersion

import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Basic

/-!
# The boundary contour at the ceiling corner

The contour passes through the ceiling's left corner `-1/2 + H·i` only at the parameter
`t = 4`, an interior parameter, so the Cauchy-kernel principal value there exists. The
corner is the junction of the left vertical with the truncation ceiling; it is the one
non-elliptic point of the contour at which the residue side may place a singular point,
and unlike the elliptic points its winding contribution is not needed — only the existence
of the principal value.

## Main declarations

* `TauCeti.ModularForm.eq_four_of_fdBoundary_eq_ceiling_corner`: the contour reaches the
  corner only at `t = 4`.
* `TauCeti.ModularForm.cauchyPVExistsAt_fdBoundary_ceiling_corner`: the Cauchy-kernel
  principal value at the corner exists.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/OnCurvePV/EndpointCorner.lean`) this file ports
  onto the current Mathlib pin; the principal value itself comes from the contour library's
  immersion criterion rather than the source's bespoke limit argument.
-/

public section

open Complex Set

namespace TauCeti

namespace ModularForm

variable {H t : ℝ}

/-- The ceiling advances the real part affinely from the left corner. -/
private lemma re_fdBoundary_of_mem_Icc_four_five (H : ℝ) {t : ℝ} (ht : t ∈ Icc (4 : ℝ) 5) :
    (fdBoundary H t).re = t - 4 - 1 / 2 := by
  rw [eqOn_fdBoundary_segment5 H ht, fdBoundary_segment5_apply, AffineMap.lineMap_apply]
  simp [Complex.real_smul]
  ring

/-- **The contour reaches the ceiling corner only at `t = 4`.** Below the corner the real
part is bounded away from `-1/2` except on the left vertical, where the height is below the
ceiling until the corner itself; above it the height is the ceiling's but the real part
increases. -/
theorem eq_four_of_fdBoundary_eq_ceiling_corner (hH : Real.sqrt 3 / 2 < H)
    (ht : t ∈ Icc (0 : ℝ) 5) (heq : fdBoundary H t = -1 / 2 + H * Complex.I) : t = 4 := by
  have him : (fdBoundary H t).im = H := by rw [heq]; simp
  have hre : (fdBoundary H t).re = -1 / 2 := by rw [heq]; simp
  rcases le_or_gt t 4 with h4 | h4
  · rcases le_or_gt t 1 with h1 | h1
    · rw [im_fdBoundary_of_le_one h1] at him
      have ht0 : t = 0 := by nlinarith [ht.1]
      rw [ht0, re_fdBoundary_segment1 H ⟨le_rfl, by norm_num⟩] at hre
      norm_num at hre
    · rcases le_or_gt t 3 with h3 | h3
      · exfalso
        have hnorm : ‖fdBoundary H t‖ = 1 := norm_fdBoundary_arc h1.le h3
        have hsq : ‖fdBoundary H t‖ ^ 2 =
            (fdBoundary H t).re ^ 2 + (fdBoundary H t).im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          ring
        rw [hnorm, hre, him] at hsq
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
      · rw [im_fdBoundary_of_le_four h3 h4] at him
        have hpos : 0 < H - Real.sqrt 3 / 2 := by linarith
        nlinarith
  · rw [re_fdBoundary_of_mem_Icc_four_five H ⟨h4.le, ht.2⟩] at hre
    linarith

/-- **The Cauchy-kernel principal value at the ceiling corner exists.** The contour is a
piecewise-`C¹` immersion meeting the corner only at the interior parameter `4`, so the
contour library's immersion criterion applies directly. -/
theorem cauchyPVExistsAt_fdBoundary_ceiling_corner (hH : Real.sqrt 3 / 2 < H) :
    Contour.CauchyPVExistsAt (fdBoundary H) 0 5
      (fun z => (z - (-1 / 2 + H * Complex.I))⁻¹) (-1 / 2 + H * Complex.I) := by
  refine (isPwC1ImmersionOn_fdBoundary (ne_of_gt hH)).cauchyPVExistsAt_inv_sub
    (by norm_num) fun t ht heq => ?_
  rw [eq_four_of_fdBoundary_eq_ceiling_corner hH ht heq]
  exact ⟨by norm_num, by norm_num⟩

end ModularForm

end TauCeti

end
