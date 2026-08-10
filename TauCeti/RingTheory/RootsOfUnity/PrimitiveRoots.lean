/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The roots of unity in a domain, given a primitive one

In a domain the `n`-th roots of unity are exactly the powers of a primitive one. Two consequences
of that, neither in Mathlib:

* a ring endomorphism is pinned down on all of them by its value on a single primitive `n`-th
  root — if it raises that root to the `j`-th power, it raises every `n`-th root to the `j`-th;
* the group `μ_n`, written additively, is `ZMod n`.

## Main results

* `TauCeti.IsPrimitiveRoot.map_eq_pow`: a ring endomorphism sending a primitive `n`-th root of
  unity `ζ` to `ζ ^ j` sends every `n`-th root of unity `μ` to `μ ^ j`.
* `TauCeti.IsPrimitiveRoot.rootsOfUnityAddEquivZMod`: `Additive (rootsOfUnity n R) ≃+ ZMod n`,
  with `rootsOfUnityAddEquivZMod_apply_zpow` and `_symm_apply_zpow`/`_symm_apply_pow` computing it
  and its inverse on powers of `ζ`.

## Provenance

`rootsOfUnityAddEquivZMod` is ported from the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by `TauCetiRoadmap/EllipticCurves` at
`dev/hasse-weil @ 513e83879e2f`), `HasseWeil/WeilPairing/RootsOfUnity.lean`, declaration
`rootsOfUnity_addEquiv_zmod`. The source states it over a field and inside an elliptic-curve
namespace; here it is over an integral domain and hangs off `IsPrimitiveRoot`. The source's proof
transports along `zpowers_eq` with `▸`; this composes instead, since a term behind `Eq.rec` does
not reduce and the characterisation lemmas above would not be provable about it.

Mathlib has both halves of the second: `IsPrimitiveRoot.zmodEquivZPowers` identifies `ZMod n` with
the `zpowers` of the root, and `IsPrimitiveRoot.zpowers_eq` identifies those with
`rootsOfUnity n R`. The additive reading is what a consumer wants when the multiplicative group is
a *codomain* rather than an object of interest: a pairing valued in `μ_n` becomes one valued in
`ZMod n`, where the linear algebra lives.
-/

public section

namespace TauCeti

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A ring homomorphism that raises one primitive `n`-th root of unity to the `j`-th power raises
every `n`-th root of unity to the `j`-th power, since the `n`-th roots of unity are exactly the
powers of a primitive one. -/
theorem IsPrimitiveRoot.map_eq_pow {n j : ℕ} [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (σ : R →+* R) (hσ : σ ζ = ζ ^ j) {μ : R} (hμ : μ ^ n = 1) : σ μ = μ ^ j := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **The `n`-th roots of unity, additively, are `ZMod n`.** For a domain with a primitive `n`-th
root of unity `ζ`, the group `μ_n` written additively is isomorphic to `ZMod n`. -/
noncomputable def IsPrimitiveRoot.rootsOfUnityAddEquivZMod {n : ℕ} [NeZero n] {ζ : Rˣ}
    (hζ : IsPrimitiveRoot ζ n) :
    Additive (rootsOfUnity n R) ≃+ ZMod n :=
  (hζ.zmodEquivZPowers.trans
    (MulEquiv.toAdditive (MulEquiv.subgroupCongr hζ.zpowers_eq))).symm

/-- The inverse sends `i : ℤ` to the root `ζ ^ i`, matching Mathlib's
`IsPrimitiveRoot.zmodEquivZPowers_symm_apply_zpow`. -/
@[simp]
theorem IsPrimitiveRoot.rootsOfUnityAddEquivZMod_symm_apply_zpow {n : ℕ} [NeZero n] {ζ : Rˣ}
    (hζ : IsPrimitiveRoot ζ n) (i : ℤ) :
    ((Additive.toMul ((IsPrimitiveRoot.rootsOfUnityAddEquivZMod hζ).symm (i : ZMod n)) :
      rootsOfUnity n R) : Rˣ) = ζ ^ i := by
  simp [IsPrimitiveRoot.rootsOfUnityAddEquivZMod]

/-- The natural-power case of `rootsOfUnityAddEquivZMod_symm_apply_zpow`, matching Mathlib's
`IsPrimitiveRoot.zmodEquivZPowers_symm_apply_pow`. -/
@[simp]
theorem IsPrimitiveRoot.rootsOfUnityAddEquivZMod_symm_apply_pow {n : ℕ} [NeZero n] {ζ : Rˣ}
    (hζ : IsPrimitiveRoot ζ n) (i : ℕ) :
    ((Additive.toMul ((IsPrimitiveRoot.rootsOfUnityAddEquivZMod hζ).symm (i : ZMod n)) :
      rootsOfUnity n R) : Rˣ) = ζ ^ i := by
  simpa using IsPrimitiveRoot.rootsOfUnityAddEquivZMod_symm_apply_zpow hζ (i : ℤ)

/-- The equivalence sends the root `ζ ^ i` to `i`. -/
@[simp]
theorem IsPrimitiveRoot.rootsOfUnityAddEquivZMod_apply_zpow {n : ℕ} [NeZero n] {ζ : Rˣ}
    (hζ : IsPrimitiveRoot ζ n) (i : ℤ) (h : ζ ^ i ∈ rootsOfUnity n R) :
    IsPrimitiveRoot.rootsOfUnityAddEquivZMod hζ (Additive.ofMul ⟨ζ ^ i, h⟩) = (i : ZMod n) := by
  apply (IsPrimitiveRoot.rootsOfUnityAddEquivZMod hζ).symm.injective
  simp only [AddEquiv.symm_apply_apply]
  exact Subtype.ext
    (IsPrimitiveRoot.rootsOfUnityAddEquivZMod_symm_apply_zpow hζ i).symm

end TauCeti
