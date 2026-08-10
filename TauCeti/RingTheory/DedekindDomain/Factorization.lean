/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Complements on the multiplicity of a height one prime

Two ways of handling `Associates.count` / `FractionalIdeal.count` that Mathlib does not carry.

* `IsDedekindDomain.HeightOneSpectrum.le_count_iff_le_pow`: the multiplicity of `v` in a nonzero
  `J` is at least `k` exactly when `v ^ k` contains `J`. Mathlib already reads the multiplicity of a
  prime as divisibility — `Associates.prime_pow_dvd_iff_le` gives
  `p ^ k ∣ m ↔ k ≤ count p m.factors` and is the first step of the proof — but that is a statement
  about `Associates`, while a consumer
  comparing two multiplicities wants a containment of *ideals*. This packages the two together,
  through `Associates.mk_le_mk_iff_dvd` and `Ideal.dvd_iff_le`. It is the form in which
  multiplicities are compared across a ring extension: one shows the two ideals contain the same
  prime powers and concludes the multiplicities agree.
* `FractionalIdeal.count_spanSingleton_div`: the multiplicity of `x / y` is the difference of the
  multiplicities of `x` and `y`. Mathlib's `count` API has `count_mul`, `count_inv`, `count_pow`
  and `count_zpow` but no division form, so every consumer that clears a denominator repeats the
  same three rewrites; this states them once.

Both are general facts about an arbitrary Dedekind domain, mentioning no particular ring extension.
The `S`-integer class-group computation in
`TauCeti/RingTheory/DedekindDomain/SInteger/ClassGroup.lean` consumes both — the second at two
different rings, which is why it is stated with the ring as a variable — advancing
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 (Mordell–Weil), whose weak-Mordell–Weil argument
needs the `S`-class group to be finite.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean:381` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header.
-/
public section

namespace IsDedekindDomain.HeightOneSpectrum

/-- The multiplicity of `v` in a nonzero ideal `J` is at least `k` exactly when `v ^ k` contains
`J`. -/
theorem le_count_iff_le_pow {A : Type*} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)
    {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

end IsDedekindDomain.HeightOneSpectrum

namespace FractionalIdeal

open IsDedekindDomain

open scoped nonZeroDivisors

/-- The multiplicity of `x / y` is the difference of the multiplicities of `x` and `y`. Mathlib's
`count` API has `count_mul` and `count_inv` but no division form. -/
theorem count_spanSingleton_div {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K]
    [Algebra A K] [IsFractionRing A K] (w : HeightOneSpectrum A) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    count K w (spanSingleton A⁰ (x / y)) =
      count K w (spanSingleton A⁰ x) - count K w (spanSingleton A⁰ y) := by
  rw [div_eq_mul_inv, ← spanSingleton_mul_spanSingleton, ← spanSingleton_inv,
    count_mul K w (by simpa only [ne_eq, spanSingleton_eq_zero_iff] using hx)
      (by simpa only [ne_eq, inv_eq_zero, spanSingleton_eq_zero_iff] using hy),
    count_inv]
  ring

end FractionalIdeal

end
