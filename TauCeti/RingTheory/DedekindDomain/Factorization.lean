/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Complements on the multiplicity of a height one prime

Four facts about `Associates.count` and `FractionalIdeal.count` that Mathlib does not carry.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.le_count_associates_iff_le_pow`: the multiplicity of `v` in
  a nonzero `J` is at least `k` exactly when `v ^ k` contains `J`. The multiplicity here is
  `Associates.count`, not `FractionalIdeal.count` — hence the `associates` token, matching
  Mathlib's `Ideal.count_associates_factors_eq` for the same expression. Mathlib reads that
  multiplicity as divisibility of `Associates`; a consumer comparing two multiplicities across a
  ring extension wants a containment of *ideals*, and shows the two ideals contain the same prime
  powers.
* `FractionalIdeal.count_div`: the multiplicity of `I / J` is the difference of the multiplicities
  of `I` and `J`. Mathlib's `count` API has `count_mul`, `count_inv`, `count_pow` and `count_zpow`
  but no division form, so every consumer that clears a denominator repeats the same rewrites.
* `FractionalIdeal.count_spanSingleton_div`: the same on principal fractional ideals. This is the
  one the `S`-integer class-group computation in
  `TauCeti/RingTheory/DedekindDomain/SInteger/ClassGroup.lean` uses, at both `R` and `𝒪_S` — which
  is why the ring is a variable rather than fixed — advancing
  `TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 (Mordell–Weil), whose weak-Mordell–Weil
  argument needs the `S`-class group to be finite. `count_div` is its general form and has no
  consumer in this repository yet.
* `FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation`: the multiplicity at `v` of the
  principal fractional ideal of a nonzero rational function `u : Kˣ` is
  `-WithZero.log (v.valuation K u)`. This is the passage between the two ways this library measures
  a principal ideal at a height one prime — Mathlib's `count` and the adic valuation.

All four are general facts about an arbitrary Dedekind domain, mentioning no particular ring
extension.

`le_count_associates_iff_le_pow` is adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean:381` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header.
**`count_div` and `count_spanSingleton_div` are new here** — they have no counterpart in that
source. `count_toPrincipalIdeal_eq_neg_log_valuation` is this repository's own, relocated here
from `TauCeti/AlgebraicGeometry/WeilDivisor/Dedekind/Basic.lean`: nothing in its statement or
proof mentions a Weil divisor, and stating it under `TauCeti.AlgebraicGeometry` put it out of
reach of the `RingTheory` consumers that need it, which is exactly the boundary
`TauCeti/RingTheory/ClassGroup/HeightOneSpectrum.lean` records in its module docstring.
-/
public section

namespace IsDedekindDomain.HeightOneSpectrum

/-- The multiplicity of `v` in a nonzero ideal `J` is at least `k` exactly when `v ^ k` contains
`J`. -/
theorem le_count_associates_iff_le_pow {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

end IsDedekindDomain.HeightOneSpectrum

namespace FractionalIdeal

open IsDedekindDomain

open scoped nonZeroDivisors

/-- **The multiplicity of a quotient is the difference of the multiplicities.** Mathlib's `count`
API has `count_mul`, `count_inv`, `count_pow` and `count_zpow` but no division form, so every
consumer that clears a denominator repeats the same rewrites. -/
theorem count_div {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (w : HeightOneSpectrum A) {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0)
    (hJ : J ≠ 0) : count K w (I / J) = count K w I - count K w J := by
  rw [div_eq_mul_inv, count_mul K w hI (inv_ne_zero hJ), count_inv]
  ring

/-- The multiplicity of `x / y` is the difference of the multiplicities of `x` and `y`: `count_div`
read on principal fractional ideals, which is the form the `S`-integer class-group computation
uses. -/
theorem count_spanSingleton_div {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K]
    [Algebra A K] [IsFractionRing A K] (w : HeightOneSpectrum A) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    count K w (spanSingleton A⁰ (x / y)) =
      count K w (spanSingleton A⁰ x) - count K w (spanSingleton A⁰ y) := by
  rw [← spanSingleton_div_spanSingleton, count_div K w (spanSingleton_ne_zero_iff.mpr hx)
    (spanSingleton_ne_zero_iff.mpr hy)]

section PrincipalIdeal

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K]

private lemma toPrincipalIdeal_eq_spanSingleton_inv_mul_span_mk'_num (u : Kˣ) (n : A) (d : A⁰)
    (hnd : IsLocalization.mk' K n d = (u : K)) :
    (toPrincipalIdeal A K u : FractionalIdeal A⁰ K) =
      spanSingleton A⁰ ((algebraMap A K) (d : A))⁻¹ * ↑(Ideal.span {n} : Ideal A) := by
  rw [coe_toPrincipalIdeal, ← hnd, IsFractionRing.mk'_eq_div, ← spanSingleton_div_spanSingleton,
    div_spanSingleton, coeIdeal_span_singleton]

private lemma valuation_mk'_eq_intValuation_div (v : HeightOneSpectrum A) (n : A) (d : A⁰) :
    v.valuation K (IsLocalization.mk' K n d) = v.intValuation n / v.intValuation (d : A) :=
  v.valuation_of_mk'

private lemma count_spanSingleton_eq_neg_log_intValuation (v : HeightOneSpectrum A) (r : A)
    (hr : r ≠ 0) :
    count K v (spanSingleton A⁰ (algebraMap A K r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal A) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← coeIdeal_span_singleton (S := A⁰) (P := K) r, count_coe K v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private lemma spanSingleton_ne_zero_of_ne_zero (r : A) (hr : r ≠ 0) :
    spanSingleton A⁰ (algebraMap A K r) ≠ 0 := by
  rw [spanSingleton_ne_zero_iff]
  intro h
  exact hr ((IsLocalization.injective K (le_refl A⁰)) (by simpa using h))

private lemma count_spanSingleton_inv_eq_log_intValuation (v : HeightOneSpectrum A) (r : A)
    (hr : r ≠ 0) :
    count K v (spanSingleton A⁰ (algebraMap A K r))⁻¹ = WithZero.log (v.intValuation r) := by
  rw [count_inv, count_spanSingleton_eq_neg_log_intValuation K v r hr]
  ring

private lemma count_spanSingleton_inv_mul_spanSingleton_eq_neg_log_div (v : HeightOneSpectrum A)
    (n d : A) (hn : n ≠ 0) (hd : d ≠ 0) :
    count K v (spanSingleton A⁰ ((algebraMap A K d)⁻¹) * spanSingleton A⁰ (algebraMap A K n)) =
      -WithZero.log (v.intValuation n / v.intValuation d) := by
  have hnI := spanSingleton_ne_zero_of_ne_zero K n hn
  have hdI := spanSingleton_ne_zero_of_ne_zero K d hd
  rw [← spanSingleton_inv K (algebraMap A K d), count_mul K v (inv_ne_zero hdI) hnI,
    count_spanSingleton_inv_eq_log_intValuation K v d hd,
    count_spanSingleton_eq_neg_log_intValuation K v n hn,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero d hd)]
  ring

/-- **The multiplicity of a principal fractional ideal is the sign-flipped logarithm of the
valuation.** Stated at the multiplicative-units level `u : Kˣ`, matching Mathlib's
`toPrincipalIdeal A K : Kˣ →* _`. -/
theorem count_toPrincipalIdeal_eq_neg_log_valuation (v : HeightOneSpectrum A) (u : Kˣ) :
    count K v (toPrincipalIdeal A K u : FractionalIdeal A⁰ K) =
      -WithZero.log (v.valuation K (u : K)) := by
  set k : K := (u : K) with hk
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq A⁰ k
  have hn : n ≠ 0 := by
    intro hn
    have hk0 : k ≠ 0 := Units.ne_zero _
    apply hk0
    rw [← hnd, hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  have hd : (d : A) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hrepr : (toPrincipalIdeal A K u : FractionalIdeal A⁰ K) =
      spanSingleton A⁰ ((algebraMap A K) (d : A))⁻¹ * ↑(Ideal.span {n} : Ideal A) :=
    toPrincipalIdeal_eq_spanSingleton_inv_mul_span_mk'_num K u n d (by rw [hnd, hk])
  have hval : v.valuation K k = v.intValuation n / v.intValuation (d : A) := by
    rw [← hnd]
    exact valuation_mk'_eq_intValuation_div K v n d
  rw [hval, hrepr, coeIdeal_span_singleton]
  exact count_spanSingleton_inv_mul_spanSingleton_eq_neg_log_div K v n d hn hd

end PrincipalIdeal

end FractionalIdeal

end
