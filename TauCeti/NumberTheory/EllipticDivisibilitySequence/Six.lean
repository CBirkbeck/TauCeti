/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# The sixth term of a normalised elliptic divisibility sequence

Mathlib computes the terms of `normEDS` up to the fourth (`normEDS_zero`, `normEDS_one`,
`normEDS_two`, `normEDS_three`, `normEDS_four`) and stops. This file adds the sixth,

`normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c`,

expressed through the fifth rather than expanded: the fifth term has no short closed form, and the
shape above is the one the divisibility arguments downstream consume.

The proof is the doubling identity `normEDS_mul_complEDS₂` at `k = 3`, after which Mathlib's
`complEDS₂_three` and `normEDS_three` evaluate the two factors.

Adapted from J. Xu's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, path
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`), declaration
`normEDS_six_eq_mul`. That file's header reads `Authors: Junyan Xu`; following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.

**Adaptations:** converted to this repository's module system, and restated for Mathlib's current
names — the source predates the rename of `compl₂EDS` to `complEDS₂` and of
`normEDS_mul_compl₂EDS` to `normEDS_mul_complEDS₂`. The source also unfolds `compl₂EDS` and
re-evaluates it at `3` from the `preNormEDS` values; Mathlib now has `complEDS₂_three`, so that
step is a rewrite rather than a computation.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (b c d : R)

/-- **The sixth term of a normalised elliptic divisibility sequence**, through the fifth:
`W₆ = (W₅ - d²) b c`. This continues Mathlib's `normEDS_zero` through `normEDS_four`, which stop
at the fourth term. -/
theorem normEDS_six_eq_mul : normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  rw [show (6 : ℤ) = 2 * 3 by rfl, ← normEDS_mul_complEDS₂, complEDS₂_three, normEDS_three]
  norm_num [normEDS, Int.even_iff]
  ring

end WeierstrassCurve

end
