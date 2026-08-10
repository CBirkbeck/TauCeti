/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Elementary facts about `dslope`

Divided-slope facts that need no differentiability, collected for the Schwarz-lemma consumers.
Away from its base point `dslope` is the plain difference quotient, so these are statements about
a normed field and its norm, with no calculus in them.

## Main results

* `TauCeti.norm_dslope_zero_eq_one_of_norm_map_eq`: a map fixing the origin has unimodular
  difference quotient at any point where it preserves the modulus. This is the hypothesis the
  equality case of Schwarz's lemma (`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`) takes,
  and the two Tau Ceti consumers of that equality case — the Schwarz--Pick rigidity theorem and
  the classification of the disc rotations — reach it by exactly this route.
-/

public section

namespace TauCeti

/-- **A map fixing the origin has unit difference quotient wherever it preserves the modulus.**
For `g 0 = 0` and `ξ ≠ 0` with `‖g ξ‖ = ‖ξ‖`, the difference quotient `dslope g 0 ξ` is
unimodular.

No differentiability is involved: at a point other than the base point `dslope` is the plain
difference quotient. -/
lemma norm_dslope_zero_eq_one_of_norm_map_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {g : 𝕜 → 𝕜} {ξ : 𝕜} (hg0 : g 0 = 0) (hξ : ξ ≠ 0) (hnorm : ‖g ξ‖ = ‖ξ‖) :
    ‖dslope g 0 ξ‖ = 1 := by
  rw [dslope_of_ne _ hξ, slope_def_field, hg0, sub_zero, sub_zero, norm_div, hnorm,
    div_self (norm_ne_zero_iff.mpr hξ)]

end TauCeti
