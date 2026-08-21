/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.NormEDS

/-!
# The division polynomial `ψ` as a normalised EDS

Mathlib defines `WeierstrassCurve.ψ` as `normEDS` at the curve's division-polynomial parameters,
but keeps the body unexposed, so no importing module can see the identification by unfolding.
This file states it, at the level of functions, and draws the one consequence that needs nothing
else: the `ψ` family is an elliptic sequence.

These two facts depend only on Mathlib's `DivisionPolynomial/Basic.lean` and this repository's
`EllipticDivisibilitySequence/NormEDS.lean`, so they sit at exactly that level — below both the
`ω` development (`DivisionPolynomial/Omega.lean`, whose `ω_spec` rewrites through the function
form) and the universal-curve transports (`DivisionPolynomial/Universal.lean`, whose elliptic
sequence statement over `Universal.Field` factors through the same identification).

## Main results

* `WeierstrassCurve.ψ_eq_normEDS`: `W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)`, as functions.
* `WeierstrassCurve.isEllipticNet_ψ`: the `ψ` family is an elliptic net.

## Provenance

`isEllipticNet_ψ` adapts J. Xu and D. K. Angdinata's
`LutzNagell/DivisionPolynomialOmega.lean` in AINTLIB (`github.com/CBirkbeck/AINTLIB`,
Apache-2.0, `main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declaration `isEllSequence_ψ`.
It is **strengthened rather than transcribed**: the source states the `s = 0` shift, and the net
holds by the identical one-line route through `isEllipticNet_normEDS`. Its consumers are the
scalar-multiplication development's addition formulas, and those need the nonzero shift, so the
sequence form is not kept alongside — `IsEllipticNet.isEllipticSequence` recovers it. This is
the same call `DivisionPolynomial/Universal.lean` already made on the source's
`isEllSequence_ψᵤ`. That file's header reads
`Authors: Junyan Xu, David Kurniadi Angdinata`; following this repository's convention for
adapted material the upstream authorship is credited here rather than in the copyright header.
`ψ_eq_normEDS` has no source counterpart: the source unfolds `ψ` where it needs this, which the
module system rejects across file boundaries, so the identification is a named `rfl` here.
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The `ψ` family is `normEDS` at the curve's division-polynomial parameters, stated at the
level of functions for rewriting under function-valued arguments such as
`IsEllipticNet.invarDenom`, where the per-application equation cannot fire. -/
theorem ψ_eq_normEDS : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl

/-- **The `ψ` family of division polynomials is an elliptic net.** The elliptic-*sequence*
consequence is the last index held at `0`, which `IsEllipticNet.isEllipticSequence` reads off;
consumers needing a nonzero shift, as the addition formula for `n • (X, Y)` does, need the net. -/
theorem isEllipticNet_ψ : IsEllipticNet W.ψ :=
  isEllipticNet_normEDS _ _ _

end WeierstrassCurve
