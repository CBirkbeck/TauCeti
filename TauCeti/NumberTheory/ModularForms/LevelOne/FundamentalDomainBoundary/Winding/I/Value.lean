/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.NonCorner

/-!
# The winding number of the boundary contour at `i`

The generalized winding number of the truncated-fundamental-domain boundary about the
elliptic point `i` is `-1/2`, with Cauchy principal value `-πi`. The elliptic point is an
interior point of the open unit arc — `‖i‖ = 1`, `|re i| = 0 < 1/2`, `0 < im i` — so both
values specialize the open-arc theorems of `Winding/NonCorner.lean`, whose `1 < H`
hypothesis is this file's own. The two statements keep their established names, and the
winding value stays the `simp`-normal anchor at the closed point `i`.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_I` (the principal value `-πi`).
* `TauCeti.ModularForm.windingNumber_fdBoundary_I` (the winding number `-1/2`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/I.lean`) whose statements at `i`
  these are; the proofs specialize the open-arc theorems of `Winding/NonCorner.lean`.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997.
-/

public section

namespace TauCeti

namespace ModularForm

variable {H : ℝ}

/-- **The principal value at `i`**: the Cauchy principal value of the index integrand of
the boundary contour about the elliptic point `i` is `-πi` — half a full turn, as the
contour passes straight through `i` along the arc. -/
theorem hasCauchyPVAt_fdBoundary_I (hH : 1 < H) :
    Contour.HasCauchyPVAt (fdBoundary H) 0 5 (fun z ↦ (z - Complex.I)⁻¹) Complex.I
      (-(Real.pi : ℂ) * Complex.I) :=
  hasCauchyPVAt_fdBoundary_arc hH (by norm_num) (by norm_num) (by norm_num)

/-- **The winding number of the boundary contour at `i` is `-1/2`**: the elliptic point
`i` sits on the contour, and the principal-value normalization sees exactly half a
clockwise turn. -/
@[simp]
theorem windingNumber_fdBoundary_I (hH : 1 < H) :
    Contour.windingNumber (fdBoundary H) 0 5 Complex.I = -(1 / 2 : ℂ) :=
  windingNumber_fdBoundary_arc hH (by norm_num) (by norm_num) (by norm_num)

end ModularForm

end TauCeti

end
