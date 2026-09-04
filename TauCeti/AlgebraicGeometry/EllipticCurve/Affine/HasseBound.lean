/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.Algebra.QuadraticDiscriminant

/-!
# The Hasse bound, from its two arithmetic inputs

Hasse's theorem bounds the number of points of an elliptic curve over a finite field:
with `q = #𝔽_q` and `a_q = q + 1 - #E(𝔽_q)` the trace of Frobenius,

```
a_q ^ 2 ≤ 4 * q,        equivalently        |#E(𝔽_q) - q - 1| ≤ 2 * √q.
```

The proof (Silverman, *AEC*, V.1.1) has a geometric half and an arithmetic half. The geometric
half produces two facts about the degree form on `End E`: that `deg (m - n π_q) = m² - a_q m n +
q n²` is non-negative, and that `deg (1 - π_q) = #E(𝔽_q)`. The arithmetic half is Cauchy–Schwarz:
a non-negative binary quadratic form has non-positive discriminant, and here that discriminant is
exactly `a_q² - 4q`.

**This file is the arithmetic half, and only that.** It takes the two geometric facts as
hypotheses and produces the bound, so the remaining work is exactly to discharge them — which
needs the degree form and the Frobenius isogeny, and is a separate milestone. Stating the
conclusion now makes that gap precise and machine-checked rather than described.

## The hypothesis is the weak one

The non-negativity hypothesis is *not* asked for on all of `ℤ × ℤ`. It is asked for only on the
locus where a fixed non-unit `d` divides neither coordinate, because that sparse locus is all the
degree form is directly known to satisfy — the coprimality is what lets the geometric argument
count kernels on the separable locus. `Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd`
already bridges that gap, and this file is its first consumer inside the library.

Passing the hypothesis on all of `ℤ × ℤ` is therefore also fine, through
`fun r s _ _ => h r s`.

## Main results

* `TauCeti.WeierstrassCurve.Affine.hasse_bound_sq_of_nonneg_on_not_dvd`: the integer form
  `(#E(𝔽_q) - q - 1) ^ 2 ≤ 4 * q`. This is the roadmap's formalisation goal.
* `TauCeti.WeierstrassCurve.Affine.hasse_bound_of_nonneg_on_not_dvd`: the real form
  `|#E(𝔽_q) - q - 1| ≤ 2 * √q`, which follows.

## Generality, and where finiteness lives

Stated over an arbitrary commutative ring and an arbitrary affine Weierstrass curve. Neither a
field, nor `IsElliptic`, nor finiteness is needed, because the arithmetic half uses none of them —
and an unused hypothesis is not available here: the linter rejects it, so a hypothesis kept only
to signal intent would have to be dropped anyway. This follows
`TauCeti.WeierstrassCurve.Affine.finite_point` next door, which declined a field and `IsElliptic`
for the same reason.

Finiteness is nonetheless what makes the statement *about* `#E(𝔽_q)`: `Nat.card` reads `0` on an
infinite type, so away from a finite base both counts are junk. The theorems stay true there, but
only vacuously, for every `d`: with `Nat.card R = 0`, `hcard` forces `t = 1`, so `hnonneg` claims
`0 ≤ s ^ 2 - r * s` for all `r, s` avoiding `d`, and `s = 1` with `r = 1 + max |d| 2` gives
`1 - (1 + max |d| 2) < 0`. Those two values avoid `d` by the same mechanism the discriminant
lemma uses to thin its line. At the roadmap's instance the base is a finite field and
`finite_point` supplies `Finite W.Point`, so the count is the honest one; that instance is where
finiteness belongs, not in these signatures.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 3 ("elliptic curves over finite fields — the
Hasse bound"), which names the integer inequality `a_q² ≤ 4q` as "the natural formalisation goal"
and its blueprint node `hasse-bound-from-witnesses` as the witness-parametric form. The names here
are the roadmap's identifier for the milestone, as with `finite_point`.

## Provenance

The witness-parametric shape is that of the AINTLIB `HasseWeil` project (Apache-2.0), revision
`513e83879e2f`, files `HasseWeil/HasseBound.lean` (`trace_sq_le_four_mul_deg`,
`abs_le_two_sqrt_of_sq_le`) and `HasseWeil/Hasse/QuadraticForm.lean`
(`traceOfFrobenius_sq_le_of_qf_nonneg`, `hasse_bound_of_qf_nonneg_witnesses`,
`hasse_bound_sq_of_qf_nonneg_witnesses`).

The statements here are strictly stronger and the proofs are not the source's. The source assumes
non-negativity on all of `ℤ × ℤ` and derives the discriminant bound by `nlinarith` on a single
substitution; this asks for non-negativity only on the not-`d`-divisible locus and routes through
`Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd`, already in the library from the same
source's `WeilPairing/Discriminant.lean`. The source's `trace_sq_le_four_mul_deg` is therefore not
carried: it is the `d`-free special case, and `Mathlib.discrim` states the same content.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.1.1 and V.1.2.
-/

public section

namespace TauCeti

namespace WeierstrassCurve

namespace Affine

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve.Affine R)

/-- **The Hasse bound, integer form**: `(#E(𝔽_q) - q - 1) ^ 2 ≤ 4 * q`.

The two hypotheses are the geometric inputs of Silverman V.1.1: `hcard` is
`deg (1 - π_q) = #E(𝔽_q)` written out with `t` the trace of Frobenius, and `hnonneg` is
non-negativity of the degree form `deg (r - s π_q) = q r² - t r s + s²`, asked for only on the
locus where `d` divides neither coordinate. -/
theorem hasse_bound_sq_of_nonneg_on_not_dvd {d t : ℤ} (hd : ¬ IsUnit d)
    (hcard : (Nat.card W.Point : ℤ) = Nat.card R + 1 - t)
    (hnonneg : ∀ r s : ℤ, ¬ d ∣ r → ¬ d ∣ s →
      0 ≤ (Nat.card R : ℤ) * r ^ 2 - t * r * s + s ^ 2) :
    ((Nat.card W.Point : ℤ) - Nat.card R - 1) ^ 2 ≤ 4 * Nat.card R := by
  -- the degree form is `q r² + (-t) r s + 1 · s²`, whose discriminant is `t² - 4q`
  have hdisc : discrim (Nat.card R : ℤ) (-t) 1 ≤ 0 :=
    Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd hd fun r s hr hs ↦ by
      linarith [hnonneg r s hr hs]
  rw [discrim] at hdisc
  rw [show (Nat.card W.Point : ℤ) - Nat.card R - 1 = -t by linarith, neg_sq]
  linarith

/-- **The Hasse bound**: `|#E(𝔽_q) - q - 1| ≤ 2 * √q`, the real form of
`hasse_bound_sq_of_nonneg_on_not_dvd`. -/
theorem hasse_bound_of_nonneg_on_not_dvd {d t : ℤ} (hd : ¬ IsUnit d)
    (hcard : (Nat.card W.Point : ℤ) = Nat.card R + 1 - t)
    (hnonneg : ∀ r s : ℤ, ¬ d ∣ r → ¬ d ∣ s →
      0 ≤ (Nat.card R : ℤ) * r ^ 2 - t * r * s + s ^ 2) :
    |(Nat.card W.Point : ℝ) - Nat.card R - 1| ≤ 2 * Real.sqrt (Nat.card R) := by
  have hsq : ((Nat.card W.Point : ℝ) - Nat.card R - 1) ^ 2 ≤ (2 * Real.sqrt (Nat.card R)) ^ 2 := by
    have h := hasse_bound_sq_of_nonneg_on_not_dvd W hd hcard hnonneg
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg' (Nat.card R))]
    have h' : ((Nat.card W.Point : ℝ) - Nat.card R - 1) ^ 2 ≤ 4 * (Nat.card R : ℝ) := by
      exact_mod_cast h
    linarith
  rw [abs_le]
  exact abs_le_of_sq_le_sq' hsq (by positivity)

end Affine

end WeierstrassCurve

end TauCeti
