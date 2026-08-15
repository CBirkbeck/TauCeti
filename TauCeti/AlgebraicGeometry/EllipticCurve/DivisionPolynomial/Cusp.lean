/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Division polynomials of the cusp curve

The cusp curve `Y² = X³` has every coefficient zero, so its low division polynomials collapse to
their leading terms: each `bᵢ` vanishes and only the monomial that carries no `bᵢ` survives.

## Main results

* `WeierstrassCurve.cusp_ψ₂`, `.cusp_Ψ₃`, `.cusp_preΨ₄`: `ψ₂ = 2Y`, `Ψ₃ = 3X⁴` and
  `preΨ₄ = 2X⁶` on the cusp curve.

## Implementation notes

`cusp`'s definition body is unexposed, so these proofs do not unfold it — they project through the
`@[simp]` lemmas `cusp_a₁` … `cusp_a₆` that `Weierstrass.lean` provides for exactly this purpose.
The `bᵢ` are then reduced by unfolding, which is available because Mathlib's
`DivisionPolynomial/Basic.lean` marks its section `@[expose]`.

## Provenance

Adapted from `LutzNagell/ZSMul.lean` in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at
`dev/modular-curves @ 9fec8eba7652` — the revision `TauCetiRoadmap/EllipticCurves/README.md` pins
for the NagellLutz project. Declarations `cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄`. That file's header
reads `Authors: David Kurniadi Angdinata, Junyan Xu`; following this repository's convention for
adapted material the upstream authorship is credited here rather than in the copyright header.

Two changes from the source. The statements are generalised from `cusp ℤ` to `cusp R` over any
`CommRing R` — nothing in them is specific to `ℤ`. And the source unfolds `cusp` directly
(`simp [cusp, ψ₂, …]`), which is not available across a module boundary; the projection lemmas
are used instead.
-/

public section

noncomputable section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable (R : Type*) [CommRing R]

/-- On the cusp curve `Y² = X³`, the `2`-division polynomial is `2Y`. -/
@[simp]
lemma cusp_ψ₂ : (cusp R).ψ₂ = 2 * Y := by
  simp [ψ₂, Affine.polynomialY, C_ofNat]

/-- On the cusp curve `Y² = X³`, the `3`-division polynomial is `3X⁴`. -/
@[simp]
lemma cusp_Ψ₃ : (cusp R).Ψ₃ = 3 * X ^ 4 := by
  simp [Ψ₃, b₂, b₄, b₆, b₈]

/-- On the cusp curve `Y² = X³`, the auxiliary polynomial `preΨ₄` is `2X⁶`. -/
@[simp]
lemma cusp_preΨ₄ : (cusp R).preΨ₄ = 2 * X ^ 6 := by
  simp [preΨ₄, b₂, b₄, b₆, b₈]

end WeierstrassCurve
