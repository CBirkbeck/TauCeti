/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The `k`-th roots of unity of a domain, as `ℤ/k`

A primitive `k`-th root of unity generates the group of all `k`-th roots of unity, so Mathlib's
`IsPrimitiveRoot.zmodEquivZPowers`, which identifies `ℤ/k` with the powers of a chosen primitive
root, identifies it with the whole of `μ_k`.

Both halves are in Mathlib — `IsPrimitiveRoot.zmodEquivZPowers` and `IsPrimitiveRoot.zpowers_eq` —
but not the composite, which is what a consumer phrased in terms of `μ_k` rather than a chosen
generator needs. Composing them through `MulEquiv.subgroupCongr` rather than rewriting along
`zpowers_eq` keeps the underlying function reducible, which is what makes the characterisation
below hold by `simp` rather than by transport.

## Main results

* `IsPrimitiveRoot.zmodEquivRootsOfUnity`: `ℤ/k ≃+ Additive (μ_k)`, given a primitive `k`-th root.
* `IsPrimitiveRoot.coe_zmodEquivRootsOfUnity_intCast`: it sends `i` to `ζ ^ i`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md:614` pins the Weil pairing as an additive bilinear map
into `Additive (rootsOfUnity N K)`, while the determinant–degree congruence that closes the Hasse
bound works with the symplectic form on the `ℓ`-torsion valued in `ℤ/ℓ`. This equivalence is the
bridge between those two codomains, and is a prerequisite of that Layer 2 target rather than the
target itself.

## Provenance

Ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) @
`a302aeacd86053f9d5f991fbbf664e1cc1051d08`, source file
`projects/HasseWeil/HasseWeil/HasseBound/WeilPairing/RootsOfUnity.lean`, declaration
`rootsOfUnity_addEquiv_zmod`. Four changes: the direction is reversed to start from `ZMod k`, so
that it reads like `IsPrimitiveRoot.zmodEquivZPowers` which it extends; the base is a domain rather
than a field, which is all `zpowers_eq` asks for; the composite is formed with
`MulEquiv.subgroupCongr` in place of the source's `▸`; and the characterising `simp` lemma, which
the source does not have, is added.
-/

public section

namespace IsPrimitiveRoot

variable {R : Type*} [CommRing R] [IsDomain R] {k : ℕ} [NeZero k] {ζ : Rˣ}

/-- **`ℤ/k` is the group of `k`-th roots of unity**, written additively, once a primitive `k`-th
root of unity is chosen: that root generates `μ_k`, so `zmodEquivZPowers` already lands on all of
it. -/
noncomputable def zmodEquivRootsOfUnity (h : IsPrimitiveRoot ζ k) :
    ZMod k ≃+ Additive (rootsOfUnity k R) :=
  h.zmodEquivZPowers.trans (MulEquiv.toAdditive (MulEquiv.subgroupCongr h.zpowers_eq))

@[simp]
theorem coe_zmodEquivRootsOfUnity_intCast (h : IsPrimitiveRoot ζ k) (i : ℤ) :
    ((h.zmodEquivRootsOfUnity (i : ZMod k)).toMul : Rˣ) = ζ ^ i := by
  simp [zmodEquivRootsOfUnity]

end IsPrimitiveRoot

end
