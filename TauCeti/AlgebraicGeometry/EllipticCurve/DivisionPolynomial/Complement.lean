/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# The complement of `ψₙ` in `ψ₂ₙ`

Mathlib defines the `n`-division polynomial of a Weierstrass curve as a normalised elliptic
divisibility sequence, `W.ψ n = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n`, and supplies the
complement of a normalised EDS, `complEDS₂`, together with
`normEDS_mul_complEDS₂ : normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k)`.

This file names the curve-level instance of that complement, `W.ψc`, so that the factorisation
`ψₙ · ψcₙ = ψ₂ₙ` can be quoted without unfolding `ψ` back to `normEDS`. It follows Mathlib's own
pattern in the same area: `W.ψ` is itself a curve-level name for a `normEDS`, with `ψ_zero`,
`ψ_one`, `ψ_neg` and so on restating the corresponding `normEDS` lemmas.

## Main definitions

* `WeierstrassCurve.ψc`: the complement of `ψₙ` in `ψ₂ₙ`.

## Main results

* `WeierstrassCurve.ψ_mul_ψc`: `ψₙ · ψcₙ = ψ₂ₙ`.
* `WeierstrassCurve.ψc_neg`: `ψc` is even.

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned
by the roadmap at `dev/modular-curves @ 9fec8eba7652`:
`LutzNagell/DivisionPolynomialOmega.lean`, declarations `ψc` and `ψc_spec` (© Junyan Xu, David
Kurniadi Angdinata), which are mathlib-track material.

Only these two are ported. That file's remaining content — the `ω` family, `invar`, and the
identities relating them — rests on an `invarDenom` / `redInvar` layer that the pinned Mathlib does
not have: Mathlib's elliptic-divisibility development has since been rewritten around elliptic
*nets*, which supplies the complement API used here (`complEDS₂`, `normEDS_mul_complEDS₂`) but no
counterpart of the invariant machinery. So `ω` remains a genuine gap rather than a transcription.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

open Polynomial
open scoped Polynomial.Bivariate

/-- The complement of `ψₙ` in `ψ₂ₙ`: the division-polynomial instance of Mathlib's `complEDS₂`. -/
protected noncomputable def ψc (n : ℤ) : R[X][Y] :=
  complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

/-- The `2n`-division polynomial factors as `ψₙ` times its complement. -/
theorem ψ_mul_ψc (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) :=
  normEDS_mul_complEDS₂ ..

@[simp]
theorem ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n :=
  complEDS₂_neg ..

end WeierstrassCurve
