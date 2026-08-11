/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Complements on the multiplicity of a height one prime

Facts about `Associates.count` and `FractionalIdeal.count` that Mathlib does not carry, and the
structure theorem they add up to: the group of nonzero fractional ideals of a Dedekind domain is
free abelian on the height one primes.

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

* `FractionalIdeal.factorization`: **the group `(FractionalIdeal A⁰ K)ˣ` of nonzero fractional
  ideals is free abelian on the height one primes**, `I ↦ (v ↦ count v I)` being the isomorphism
  onto `Multiplicative (HeightOneSpectrum A →₀ ℤ)`. Mathlib has the factorization
  `I = ∏ v ^ count v I` as a `finprod` identity on fractional ideals
  (`finprod_heightOneSpectrum_factorization'`) but does not package it as a group isomorphism, and
  has no inverse construction: `ofFinsupp` builds the ideal with prescribed multiplicities, and
  `count_injective` says an ideal is determined by them. `unitOfPrime`,
  `finite_mulSupport_unitOfPrime_zpow` and `finprod_unitOfPrime_zpow_count` are the unit-level
  form of Mathlib's statement, and were private helpers of
  `TauCeti/RingTheory/ClassGroup/HeightOneSpectrum.lean` until this file gave them a home; that
  file now consumes them.

All of these are general facts about an arbitrary Dedekind domain, mentioning no particular ring
extension.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache 2.0, by Michael Stoll) at the roadmap's
pin `66889eada51a`: `le_count_associates_iff_le_pow` from `EllipticCurves/Mathlib/Basic.lean:381`,
and `toFinsupp`, `ofFinsupp`, `count_ofFinsupp`, `count_injective` and `factorization` from
`EllipticCurves/Mathlib/FractionalIdeal.lean:97-160`. Following this repository's convention for
adapted material, the upstream authorship is credited here rather than in the copyright header.
**The two `count` lemmas are new here** — they have no counterpart in that source; so is
`coe_ofFinsupp`, and `count_injective` is proved from the unit-level factorization already in this
repository rather than from that source's `prod_count`, which duplicates Mathlib's
`finprod_heightOneSpectrum_factorization'`.
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

/-! ### The group of fractional ideals is free abelian on the height one primes -/

section Factorization

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- `v.asIdeal` as an invertible fractional ideal: the shape the factorization of a unit
fractional ideal takes. -/
@[expose] noncomputable def unitOfPrime (v : HeightOneSpectrum A) : (FractionalIdeal A⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal A⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] lemma coe_unitOfPrime (v : HeightOneSpectrum A) :
    ((unitOfPrime K v : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) = v.asIdeal := rfl

variable {K}

/-- Only finitely many primes divide a unit fractional ideal, so its prime-power family has
finite multiplicative support and the factorization below is a finite product. -/
lemma finite_mulSupport_unitOfPrime_zpow (I : (FractionalIdeal A⁰ K)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum A =>
      unitOfPrime K v ^ count K v (I : FractionalIdeal A⁰ K)).Finite := by
  refine (Filter.eventually_cofinite.mp (finite_factors (I : FractionalIdeal A⁰ K))).subset
    fun v hv hc0 => ?_
  exact hv (by simp only [hc0, zpow_zero])

/-- **Unique factorization at unit level**: a unit fractional ideal is the product of the prime
powers its multiplicities record. This is Mathlib's
`FractionalIdeal.finprod_heightOneSpectrum_factorization'`, which is stated for fractional
ideals, transported to `(FractionalIdeal A⁰ K)ˣ` along `Units.coeHom`. -/
lemma finprod_unitOfPrime_zpow_count (I : (FractionalIdeal A⁰ K)ˣ) :
    I = ∏ᶠ v : HeightOneSpectrum A, unitOfPrime K v ^ count K v (I : FractionalIdeal A⁰ K) := by
  -- The `map_finprod` equation is stated rather than rewritten into, because
  -- `← Units.coeHom_apply` would also rewrite the coercion inside `count K v ↑I`.
  have hmap : ((∏ᶠ v : HeightOneSpectrum A,
        unitOfPrime K v ^ count K v (I : FractionalIdeal A⁰ K)) : (FractionalIdeal A⁰ K)ˣ) =
      ∏ᶠ v : HeightOneSpectrum A,
        ((unitOfPrime K v ^ count K v (I : FractionalIdeal A⁰ K) :
          (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) :=
    MonoidHom.map_finprod (Units.coeHom (FractionalIdeal A⁰ K))
      (finite_mulSupport_unitOfPrime_zpow I)
  refine Units.ext ?_
  rw [hmap]
  simp only [unitOfPrime, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  exact (finprod_heightOneSpectrum_factorization' (K := K)
    (I := (I : FractionalIdeal A⁰ K)) (Units.ne_zero I)).symm

/-- **A unit fractional ideal is determined by its multiplicities.** -/
lemma count_injective {I J : (FractionalIdeal A⁰ K)ˣ}
    (h : ∀ v, count K v (I : FractionalIdeal A⁰ K) = count K v (J : FractionalIdeal A⁰ K)) :
    I = J := by
  rw [finprod_unitOfPrime_zpow_count I, finprod_unitOfPrime_zpow_count J]
  exact finprod_congr fun v ↦ by rw [h v]

variable (K)

/-- The finitely supported tuple of multiplicities of a unit fractional ideal. -/
@[expose] noncomputable def toFinsupp (I : (FractionalIdeal A⁰ K)ˣ) : HeightOneSpectrum A →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ count K v (I : FractionalIdeal A⁰ K)) (by
    have := finite_factors (I : FractionalIdeal A⁰ K)
    simpa [Function.support, Filter.eventually_cofinite] using this)

@[simp] lemma toFinsupp_apply (I : (FractionalIdeal A⁰ K)ˣ) (v : HeightOneSpectrum A) :
    toFinsupp K I v = count K v (I : FractionalIdeal A⁰ K) := rfl

/-- The unit fractional ideal `∏ v ^ g v` with prescribed multiplicities. -/
@[expose] noncomputable def ofFinsupp (g : HeightOneSpectrum A →₀ ℤ) : (FractionalIdeal A⁰ K)ˣ :=
  g.prod fun v e ↦ unitOfPrime K v ^ e

lemma coe_ofFinsupp (g : HeightOneSpectrum A →₀ ℤ) :
    ((ofFinsupp K g : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K)
      = g.prod fun v e ↦ (v.asIdeal : FractionalIdeal A⁰ K) ^ e := by
  rw [ofFinsupp, ← Units.coeHom_apply, map_finsuppProd]
  simp [Units.coeHom, unitOfPrime]

@[simp] lemma count_ofFinsupp (g : HeightOneSpectrum A →₀ ℤ) (v : HeightOneSpectrum A) :
    count K v ((ofFinsupp K g : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) = g v := by
  rw [coe_ofFinsupp, count_finsuppProd]

/-- **The group of nonzero fractional ideals of a Dedekind domain is free abelian on the height
one primes**, the isomorphism being `I ↦ (v ↦ count v I)`. -/
@[expose] noncomputable def factorization :
    (FractionalIdeal A⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum A →₀ ℤ) where
  toFun I := Multiplicative.ofAdd (toFinsupp K I)
  invFun g := ofFinsupp K (Multiplicative.toAdd g)
  left_inv I := count_injective fun v ↦ by rw [count_ofFinsupp]; rfl
  right_inv g := by
    apply Multiplicative.toAdd.injective
    ext
    simp only [toAdd_ofAdd, toFinsupp_apply, count_ofFinsupp]
  map_mul' I J := by
    apply Multiplicative.toAdd.injective
    ext v
    simp only [toAdd_ofAdd, Finsupp.coe_add, Pi.add_apply, toFinsupp_apply, Units.val_mul,
      toAdd_mul]
    exact count_mul K v (Units.ne_zero I) (Units.ne_zero J)

@[simp] lemma factorization_apply (I : (FractionalIdeal A⁰ K)ˣ) (v : HeightOneSpectrum A) :
    Multiplicative.toAdd (factorization K I) v = count K v (I : FractionalIdeal A⁰ K) := rfl

end Factorization

end FractionalIdeal

end
