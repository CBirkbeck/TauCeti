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
  with `rootsOfUnityAddEquivZMod_symm_apply` computing its inverse as a power of `ζ`.

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

/-- The inverse sends `i` to the root `ζ ^ i`, matching Mathlib's
`IsPrimitiveRoot.zmodEquivZPowers_symm_apply_zpow`. -/
@[simp]
theorem IsPrimitiveRoot.rootsOfUnityAddEquivZMod_symm_apply {n : ℕ} [NeZero n] {ζ : Rˣ}
    (hζ : IsPrimitiveRoot ζ n) (i : ℕ) :
    ((Additive.toMul ((IsPrimitiveRoot.rootsOfUnityAddEquivZMod hζ).symm (i : ZMod n)) :
      rootsOfUnity n R) : Rˣ) = ζ ^ i := by
  simp [IsPrimitiveRoot.rootsOfUnityAddEquivZMod]

end TauCeti
