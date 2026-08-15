/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Invariant
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.NormEDS

/-!
# The invariant of a normalised EDS

`invarNum W s n / invarDenom W s n` is independent of `n` for an elliptic net `W`
(`invarNum_mul_invarDenom`, in cross-multiplied form). A normalised EDS is an elliptic net
unconditionally (`isEllipticNet_normEDS`), so the two combine, and evaluating the invariant at the
single index `n = 2` pins its value for every other index.

## Main results

* `invarNum_normEDS_two`, `invarDenom_normEDS_two`: the invariant of `normEDS b c d` at `s = 1`,
  `n = 2` is `(d + b ^ 4) * b` over `c * b`.
* `invar₂_normEDS`: the cross-multiplied consequence,
  `invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4)`, for every `m`
  and with no hypothesis on `b`, `c`, `d`.

## Implementation notes

Instantiating `invarNum_mul_invarDenom` at `(s, m, n) = (1, m, 2)` and substituting the two values
above gives the target multiplied through by `b`:

`(invarNum (normEDS b c d) 1 m * c) * b = (invarDenom (normEDS b c d) 1 m * (d + b ^ 4)) * b`

Cancelling that `b` needs `b` to be a nonzerodivisor, which is **not** implied by
`isEllipticNet_normEDS` being unconditional — that is a fact about the net property, not about
cancellation. The hypothesis is therefore discharged the same way `NormEDS.lean` discharges it for
`isEllipticNet_normEDS`: prove the statement over `MvPolynomial NormEDSParam ℤ`, where the
indeterminate `X B` *is* a nonzerodivisor, then specialise along `aeval`. `invar₂_normEDSAux` is
the hypothesis-carrying form and exists only to be specialised.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at `dev/modular-curves @ 9fec8eba7652` — the revision
`TauCetiRoadmap/EllipticCurves/README.md` pins for the NagellLutz project. Declarations
`invarNum_normEDS_two`, `invarDenom_normEDS_two`, `invar₂_normEDS_of_mem_nonZeroDivisors` and
`invar₂_normEDS`. That file's header reads `Authors: David Kurniadi Angdinata`; following this
repository's convention for adapted material the upstream authorship is credited here rather than
in the copyright header.

The source's `invar_normEDS` step is this repository's `invarNum_mul_invarDenom` applied to
`isEllipticNet_normEDS`, so no separate declaration is needed for it.
-/

public section

open MvPolynomial NormEDSParam

open scoped nonZeroDivisors

namespace IsEllipticNet

variable {R : Type*} [CommRing R] {b c d : R} {m : ℤ}

/-- The numerator of the invariant of `normEDS b c d` at `s = 1`, `n = 2`. -/
theorem invarNum_normEDS_two (b c d : R) : invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp [right_distrib, ← pow_succ, ← pow_add]

/-- The denominator of the invariant of `normEDS b c d` at `s = 1`, `n = 2`. -/
theorem invarDenom_normEDS_two (b c d : R) : invarDenom (normEDS b c d) 1 2 = c * b := by
  simp

/-- `invar₂_normEDS` under a nonzerodivisor hypothesis on `b`, which the unconditional form
discharges by specialising from the universal parameters. -/
private theorem invar₂_normEDSAux (hb : b ∈ R⁰) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb]
  have h := invarNum_mul_invarDenom (isEllipticNet_normEDS b c d) 1 m 2
  rw [invarNum_normEDS_two, invarDenom_normEDS_two] at h
  linear_combination h

/-- **The invariant of a normalised EDS, pinned at `s = 1`.** For every `m`, and with no
hypothesis on `b`, `c`, `d`. -/
theorem invar₂_normEDS (b c d : R) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  have huniv := invar₂_normEDSAux (b := (X B : MvPolynomial NormEDSParam ℤ))
    (c := X C) (d := X D) (mem_nonZeroDivisors_of_ne_zero (X_ne_zero (R := ℤ) B)) m
  have key := congr(aeval (NormEDSParam.rec b c d) $huniv)
  -- `universalNormEDS`'s body is unexposed, so the function-level equation has to be supplied;
  -- `universalNormEDS_apply` is pointwise and cannot fire under `invarNum`.
  have hfun : (universalNormEDS : ℤ → MvPolynomial NormEDSParam ℤ)
      = normEDS (X B) (X NormEDSParam.C) (X D) := funext universalNormEDS_apply
  rw [normEDS_eq_aeval (b := b) (c := c) (d := d), ← Function.comp_def, ← map_invarNum,
    ← map_invarDenom, hfun]
  simpa only [map_mul, map_add, map_pow, aeval_X] using key

end IsEllipticNet
