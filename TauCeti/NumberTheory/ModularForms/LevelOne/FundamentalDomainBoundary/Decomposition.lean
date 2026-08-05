/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.Analysis.Contour.Winding.Number.Partition

/-!
# Decomposition of the winding number of the boundary contour

For a point off the boundary contour of the truncated fundamental domain, the winding
number over the full parameter interval `[0, 5]` splits as the sum of the winding numbers
of the four smooth pieces: the right vertical, the arc, the left vertical, and the
truncation ceiling. This is the entry point for evaluating the winding number at interior
points piece by piece.

The single-point Cauchy principal values required by the partition additivity are supplied
by avoidance: away from the contour the index integrand has no singularity, and its
integrability follows from the piecewise-`C¹` regularity of the contour.

## Main declarations

* `TauCeti.ModularForm.cauchyPVExistsAt_fdBoundary`
* `TauCeti.ModularForm.windingNumber_fdBoundary_eq_sum_pieces`
-/

public section

open Set TauCeti.Contour

namespace TauCeti

namespace ModularForm

variable {H : ℝ} {w : ℂ}

/-- The single-point Cauchy principal value of the index integrand exists on every
subinterval of the parameter interval of the boundary contour, for any point `w` off the
contour: the integrand is then singularity-free, and integrable by piecewise-`C¹`
regularity. -/
theorem cauchyPVExistsAt_fdBoundary (hw : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ≠ w)
    (c d : ℝ) (hc : c ∈ Icc (0 : ℝ) 5) (hd : d ∈ Icc (0 : ℝ) 5) :
    CauchyPVExistsAt (fdBoundary H) c d (fun z => (z - w)⁻¹) w := by
  have hsub : uIcc c d ⊆ uIcc (0 : ℝ) 5 := uIcc_subset_uIcc
    (by rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)])
    (by rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)])
  have hsub' : uIcc c d ⊆ Icc (0 : ℝ) 5 := by
    rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hsub
  refine cauchyPVExistsAt_of_avoidance (continuous_fdBoundary H).continuousOn
    (fun t ht => hw t (hsub' ht)) ?_
  have hcont : ContinuousOn (fun t => (fdBoundary H t - w)⁻¹) (uIcc c d) :=
    ((continuous_fdBoundary H).continuousOn.sub continuousOn_const).inv₀
      fun t ht => sub_ne_zero.mpr (hw t (hsub' ht))
  exact ((isPiecewiseC1On_fdBoundary H).intervalIntegrable_deriv.mono_set
    hsub).continuousOn_mul hcont

/-- The winding number of the boundary contour about a point off the contour is the sum of
the winding numbers of its four smooth pieces: the right vertical, the arc, the left
vertical, and the truncation ceiling. This instantiates the finite-partition additivity
`Contour.windingNumber_eq_sum_range` at the junction partition `0, 1, 3, 4, 5`. -/
theorem windingNumber_fdBoundary_eq_sum_pieces
    (hw : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ≠ w) :
    windingNumber (fdBoundary H) 0 5 w =
      windingNumber (fdBoundary H) 0 1 w + windingNumber (fdBoundary H) 1 3 w +
        windingNumber (fdBoundary H) 3 4 w + windingNumber (fdBoundary H) 4 5 w := by
  have hpv := cauchyPVExistsAt_fdBoundary hw
  have h := windingNumber_eq_sum_range (γ := fdBoundary H) (z₀ := w) (n := 4)
    (t := fun k => match k with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | _ => 5)
    (fun k hk => by
      match k, hk with
      | 0, _ => exact hpv 0 1 ⟨le_rfl, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      | 1, _ => exact hpv 1 3 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      | 2, _ => exact hpv 3 4 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      | 3, _ => exact hpv 4 5 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      | n + 4, hk => exact absurd hk (Nat.not_lt.mpr (Nat.le_add_left 4 n)))
  refine h.trans ?_
  simp [Finset.sum_range_succ]

end ModularForm

end TauCeti

end
