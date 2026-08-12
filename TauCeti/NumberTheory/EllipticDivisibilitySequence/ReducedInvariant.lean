/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EllipticDivisibilitySequence.ComplAux
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Invariant

/-!
# The reduced invariant of a normalised EDS

For a normalised EDS `normEDS b c d`, the invariant of `IsEllipticNet` at `s = 1` carries factors
that are constant in the index: `IsEllipticNet.invarNum` is divisible by `b = W 2`, and
`IsEllipticNet.invarDenom` by `b * c = W 2 * W 3`. This file names the two quotients — `redInvarNum`
and `redInvarDenom` — and proves the cancellation for the numerator.

The numerator's reduced form is a sum rather than a quotient: `redInvarNum` is defined outright as

`redInvarNum b c d m = complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDS₂Aux b c d m`,

and `invarNum_eq_redInvarNum_mul` is what identifies it as the cancellation, `invarNum` being
`redInvarNum * b`. Reading it the other way, `complEDS₂_eq_redInvarNum_sub` expresses the second
complement through the invariant — the step by which the elliptic-net identities reach the division
polynomials in the Lutz–Nagell development.

## Main definitions

* `redInvarNum`: the invariant numerator of a normalised EDS with one factor of `b` cancelled.
* `redInvarDenom`: the corresponding denominator, `W (m + 1) * W m * W (m - 1)` with `W 3 * W 2`
  cancelled. Its definition splits on `m % 6`, because which of the three consecutive terms the
  complement sequences divide depends on that residue.

## Main results

* `IsEllipticNet.invarNum_eq_redInvarNum_mul`: `invarNum (normEDS b c d) 1 m` is
  `redInvarNum b c d m * b` — the cancellation the reduced numerator is named for.
* `complEDS₂_eq_redInvarNum_sub`: the second complement read off the reduced numerator.
* `IsEllipticNet.invarNum_normEDS`: the invariant numerator of a normalised EDS at `s = 1`, with
  `W 1 = 1` and `W 2 = b` substituted. This is a measured prerequisite of
  `invarNum_eq_redInvarNum_mul` rather than an addition: that proof cancels `b` against the
  substituted `W 2`, so the substituted form has to exist first. The source names it for the same
  reason, and the blocked layer's `invarNum_normEDS_two` and `invarDenom_normEDS_two` are the same
  shape at a fixed index.

## What is deliberately not here

The two results that would connect `redInvarNum` and `redInvarDenom` to each other —
`redInvar_normEDS` (`redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4)`) and
`invarDenom_eq_redInvarDenom_mul` — are **not** in this file, and are not an oversight. Both route
through the fact that `normEDS` is an elliptic sequence, along

`redInvar_normEDS ← invar₂_normEDS ← invar_normEDS ← net_normEDS ← IsEllipticSequence.normEDS`

for the first, and `invarDenom_eq_redInvarDenom_mul ← normEDS_mul_complEDS_div ←
normEDS_mul_complEDS ← normEDS_mul_complEDS_of_mem ← IsEllipticSequence.normEDS` for the second.
That fact is not in the pinned Mathlib, which records it as an open TODO
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`: "prove that `normEDS` satisfies
`IsEllipticDvdSequence`"), and proving it needs the parity-transfer machinery of Mathlib PR #42453.
Everything in this file is independent of it: nothing below carries an ellipticity hypothesis, and
the source discharges the ellipticity variables over exactly this block.

## Provenance

Ported from J. Xu's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `invarNum_normEDS`, `redInvarNum`,
`compl₂EDS_eq_redInvarNum_sub`, `invarNum_eq_redInvarNum_mul` and `redInvarDenom`. That file's
header reads `Authors: Junyan Xu`; following this repository's convention for adapted material the
upstream authorship is credited here rather than in the copyright header.

The same declarations sit in **Mathlib PR #13057** (open, last updated 2024-07-31), the upstreaming
of that AINTLIB file, so they are portable under this project's rule and deduplicate when it lands.
They are spelt with Mathlib's later names (`compl₂EDS → complEDS₂`, `IsEllSequence →
IsEllipticSequence`), which #13057 predates, and follow `ComplAux.lean` in keeping the
`normEDS`-family declarations in the **root** namespace where Mathlib keeps `normEDS`, `complEDS`
and `complEDS₂`; the two results about `IsEllipticNet.invarNum` stay in that namespace, after their
left-hand sides.

One adaptation is forced rather than chosen: the source proves `invarNum_normEDS` by
`simp [invarNum]`, unfolding the definition. That does not port, because `Invariant.lean` exports
`invarNum`'s body unexposed — from an importing module `simp [invarNum]` is rejected outright — so
the proof goes through the `@[simp]` equation lemma `IsEllipticNet.invarNum_def` instead.
-/

public section

variable {R : Type*} [CommRing R] (b c d : R) (m : ℤ)

namespace IsEllipticNet

/-- The invariant numerator of a normalised EDS at `s = 1`, with `W 1 = 1` and `W 2 = b`
substituted. -/
theorem invarNum_normEDS (n : ℤ) :
    invarNum (normEDS b c d) 1 n =
      normEDS b c d (n + 2) * normEDS b c d (n - 1) ^ 2
        + normEDS b c d (n + 1) ^ 2 * normEDS b c d (n - 2)
        + normEDS b c d n ^ 3 * b ^ 2 := by
  simp [invarNum_def]

end IsEllipticNet

/-- The invariant numerator of a normalised EDS with one factor of `b` cancelled. Stated as the sum
it reduces to rather than as a quotient; `IsEllipticNet.invarNum_eq_redInvarNum_mul` is what
identifies it as the cancellation. -/
def redInvarNum : R :=
  complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDS₂Aux b c d m

/-- The defining formula for `redInvarNum`. The definition body is not exposed, so this equation
lemma is how a consumer computes with it. It is deliberately **not** `@[simp]`, for the reason
`complEDS₂Aux_def` is not: tagging it would have `simp` unfold `redInvarNum` everywhere and defeat
the point of naming the term. -/
theorem redInvarNum_def : redInvarNum b c d m =
    complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDS₂Aux b c d m := (rfl)

/-- **The second complement read off the reduced numerator.** This is the direction the Lutz–Nagell
development uses: it expresses `complEDS₂` through the invariant of the elliptic net, rather than
through its own defining difference. -/
theorem complEDS₂_eq_redInvarNum_sub :
    complEDS₂ b c d m =
      redInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * complEDS₂Aux b c d m := by
  rw [redInvarNum_def]; ring

namespace IsEllipticNet

/-- **The cancellation `redInvarNum` is named for**: the invariant numerator of a normalised EDS at
`s = 1` is `redInvarNum` times `b`. The factor of `b` is constant in `m`, which is what makes the
reduced form the one the division-polynomial identities are stated over. -/
theorem invarNum_eq_redInvarNum_mul :
    invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b := by
  simp_rw [redInvarNum_def, right_distrib, complEDS₂_mul_b, mul_assoc 2 _ b, complEDS₂Aux_mul_b,
    invarNum_normEDS]
  ring

end IsEllipticNet

/-- The denominator `W (m + 1) * W m * W (m - 1)` of the invariant of a normalised EDS, with the
constant factor `W 3 * W 2 = c * b` cancelled.

The definition splits on `m % 6`. Among any three consecutive indices `m - 1, m, m + 1` exactly
which are divisible by `2` and by `3` depends on the residue, and the complement sequences
`complEDS b c d 2` and `complEDS b c d 3` are what carry off those factors; the residues `0`, `1`
and `5` take the sixth complement instead, with `r₆ = W 6 / (W 3 * W 2)` written as
`normEDS b c d 5 - d ^ 2`. -/
def redInvarDenom : R :=
  let C := complEDS b c d
  let W := normEDS b c d
  let r₆ := normEDS b c d 5 - d ^ 2
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1) else
  if m % 6 = 1 then r₆ * C 6 ((m - 1) / 6) * W (m + 1) * W m else
  if m % 6 = 5 then r₆ * C 6 ((m + 1) / 6) * W m * W (m - 1) else
  if m % 6 = 2 then C 3 ((m + 1) / 3) * C 2 (m / 2) * W (m - 1) else
  if m % 6 = 4 then C 3 ((m - 1) / 3) * C 2 (m / 2) * W (m + 1) else
  if m % 6 = 3 then C 3 (m / 3) * C 2 ((m - 1) / 2) * W (m + 1) else 0
