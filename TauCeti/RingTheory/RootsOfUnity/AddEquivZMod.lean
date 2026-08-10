/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The `ℓ`-th roots of unity, written additively, are `ZMod ℓ`

A field containing a primitive `ℓ`-th root of unity has `μ_ℓ` cyclic of order `ℓ`, so `μ_ℓ` written
additively is `ZMod ℓ`. Mathlib has both halves of this — `IsPrimitiveRoot.zmodEquivZPowers`
identifies `ZMod ℓ` with the `zpowers` of the root, and `IsPrimitiveRoot.zpowers_eq` identifies
those `zpowers` with `rootsOfUnity ℓ F` — but not their composite.

## Main results

* `TauCeti.rootsOfUnity_addEquivZMod`: `Additive (rootsOfUnity ℓ F) ≃+ ZMod ℓ`, from a primitive
  `ℓ`-th root of unity.

The additive reading is what a consumer wants when the multiplicative group is a *codomain* rather
than a group of interest in itself: a pairing valued in `μ_ℓ` becomes a pairing valued in `ZMod ℓ`,
where the linear algebra lives. That is the use in the Weil-pairing route to the Hasse bound of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 3, where `e_ℓ : E[ℓ] × E[ℓ] → μ_ℓ` has to meet the
symplectic form on `E[ℓ] ≅ (ZMod ℓ)²`.

No `Fintype` or characteristic hypothesis is needed: the primitive root carries all of it.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/WeilPairing/RootsOfUnity.lean`,
declaration `rootsOfUnity_addEquiv_zmod`.

Changes from the source. The name follows Mathlib's `AddEquiv` convention (`addEquivZMod` rather
than `addEquiv_zmod`), and the declaration is placed with Mathlib's roots-of-unity material rather
than under an elliptic-curve namespace, since neither its statement nor its proof mentions a curve.
-/

public section

namespace TauCeti

/-- **The `ℓ`-th roots of unity, additively, are `ZMod ℓ`.** For a field `F` with a primitive `ℓ`-th
root of unity `ζ`, the group `μ_ℓ` written additively is isomorphic to `ZMod ℓ`. -/
noncomputable def rootsOfUnity_addEquivZMod {F : Type*} [Field F] {ℓ : ℕ} [NeZero ℓ] {ζ : Fˣ}
    (hζ : IsPrimitiveRoot ζ ℓ) :
    Additive (rootsOfUnity ℓ F) ≃+ ZMod ℓ :=
  (hζ.zpowers_eq ▸ hζ.zmodEquivZPowers).symm

end TauCeti

end
