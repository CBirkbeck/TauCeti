/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Adic valuations transport along an isomorphism of Dedekind domains

An isomorphism `e : R ≃+* R'` of Dedekind domains induces an isomorphism
`σ = IsFractionRing.ringEquivOfRingEquiv e : K ≃+* K'` of their fraction fields, and carries a
height one prime `v` of `R` to the height one prime of `R'` with underlying ideal
`Ideal.map e v.asIdeal`. This file proves that `σ` intertwines the two adic valuations: for a
height one prime `w` of `R'` with
`w.asIdeal = Ideal.map e v.asIdeal`,

```text
w.valuation K' (σ f) = v.valuation K f
```

for every `f : K`. Equivalently, `ord` at `w` of `σ f` is `ord` at `v` of `f`, which is the
algebraic content of the Galois descent `div (σ f) = σ_* (div f)` for divisors on a curve.

## Main results

* `Ideal.map_dvd_map_iff_of_ringEquiv` and `Ideal.map_pow_dvd_map_iff_of_ringEquiv`:
  divisibility of ideals, and of an ideal by a power, are unchanged by `Ideal.map e`.
* `IsDedekindDomain.HeightOneSpectrum.asIdeal_equivOfRingEquiv`: Mathlib's transport
  `equivOfRingEquiv e` of height one primes is `Ideal.map e` on the underlying ideal.
* `Ideal.count_factors_map_of_ringEquiv`: multiplicities in the factorisation are unchanged by
  `Ideal.map e`.
* `IsDedekindDomain.HeightOneSpectrum.intValuation_ringEquiv` and
  `IsDedekindDomain.HeightOneSpectrum.valuation_ringEquivOfRingEquiv`: the integer-valued and the
  fraction-field adic valuations transport.

## Implementation notes

The hypothesis on the two primes is stated as the equation `w.asIdeal = Ideal.map e v.asIdeal`
rather than as `w = equivOfRingEquiv e v`, so that a call site holding some independently
constructed `w` — a place of a curve, say — does not first have to identify it with the transport.
`asIdeal_equivOfRingEquiv` discharges the hypothesis whenever `w` *is* that transport, so nothing
is lost in the other direction.

The two divisibility lemmas are stated over plain commutative rings, in a section that does not
assume `IsDedekindDomain`: they need only that `Ideal.map e` and `Ideal.map e.symm` are mutually
inverse homomorphisms of the semirings of ideals. The factorisation and valuation results below do
use the Dedekind hypothesis, and are separated from them for that reason.

## Provenance

Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Apache-2.0), commit
`513e83879e2f`, `projects/HasseWeil/HasseWeil/WeilPairing/DivisorGalois.lean`: the proofs of
`map_dvd_iff_ringEquiv`, `pow_dvd_iff_map_ringEquiv`, `count_map_ringEquiv`,
`intValuation_map_ringEquiv`, `valuation_map_ringEquiv_algebraMap` and `valuation_map_ringEquiv`
are that file's, with the vocabulary adapted to this repository's interfaces.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, II.3 (the Galois action on divisors).
-/

public section

namespace Ideal

section CommRing

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- Divisibility of ideals is unchanged by pushing forward along a ring isomorphism: `Ideal.map e`
and `Ideal.map e.symm` are mutually inverse homomorphisms of the semirings of ideals. -/
theorem map_dvd_map_iff_of_ringEquiv (e : R ≃+* R') (I J : Ideal R) :
    Ideal.map e I ∣ Ideal.map e J ↔ I ∣ J := by
  -- `Ideal.map` sees `e` through `FunLike`, so `e` and its `RingHom` coercion give the same ideal;
  -- passing to the coercion is what lets `Ideal.mapHom` carry the divisibility.
  change Ideal.map (e : R →+* R') I ∣ Ideal.map (e : R →+* R') J ↔ I ∣ J
  refine ⟨fun h ↦ ?_, fun h ↦ by
    simpa only [mapHom_apply] using map_dvd (mapHom (e : R →+* R')) h⟩
  have hcomp : (e.symm : R' →+* R).comp (e : R →+* R') = RingHom.id R := by ext x; simp
  simpa only [mapHom_apply, Ideal.map_map, hcomp, Ideal.map_id] using
    map_dvd (mapHom (e.symm : R' →+* R)) h

/-- The prime-power divisibility `p ^ n ∣ I` is unchanged by pushing forward along a ring
isomorphism. -/
theorem map_pow_dvd_map_iff_of_ringEquiv (e : R ≃+* R') (p I : Ideal R) (n : ℕ) :
    (Ideal.map e p) ^ n ∣ Ideal.map e I ↔ p ^ n ∣ I := by
  rw [← Ideal.map_pow]
  exact map_dvd_map_iff_of_ringEquiv e (p ^ n) I

end CommRing

section DedekindDomain

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

/-- Multiplicities in the factorisation of an ideal are unchanged by pushing forward along a ring
isomorphism: the number of times `Ideal.map e p` divides `Ideal.map e I` is the number of times
`p` divides `I`. -/
theorem count_factors_map_of_ringEquiv (e : R ≃+* R') {p I : Ideal R} (hp : Prime p) (hI : I ≠ ⊥) :
    (Associates.mk (Ideal.map e p)).count (Associates.mk (Ideal.map e I)).factors =
      (Associates.mk p).count (Associates.mk I).factors := by
  classical
  have hpb : p ≠ ⊥ := by simpa only [zero_eq_bot] using hp.ne_zero
  have hpmapb : Ideal.map e p ≠ ⊥ := by
    simpa only [ne_eq, map_eq_bot_iff_of_injective e.injective] using hpb
  have hI0 : I ≠ 0 := by simpa only [zero_eq_bot] using hI
  -- `map_isPrime_of_equiv` is an instance, so it fires once `p.IsPrime` is in the context.
  have : p.IsPrime := (prime_iff_isPrime hpb).mp hp
  have hpmap : Prime (Ideal.map e p) := (prime_iff_isPrime hpmapb).mpr (map_isPrime_of_equiv e)
  have hmkImap : Associates.mk (Ideal.map e I) ≠ 0 := Associates.mk_ne_zero.mpr
    (by simpa only [ne_eq, zero_eq_bot, map_eq_bot_iff_of_injective e.injective] using hI)
  have hmkI : Associates.mk I ≠ 0 := Associates.mk_ne_zero.mpr hI0
  -- Both counts are pinned by the same `n ≤ ·` characterisation, through `prime_pow_dvd_iff_le`.
  have key : ∀ n : ℕ, n ≤ (Associates.mk (Ideal.map e p)).count
        (Associates.mk (Ideal.map e I)).factors ↔
      n ≤ (Associates.mk p).count (Associates.mk I).factors := fun n ↦ by
    rw [← Associates.prime_pow_dvd_iff_le hmkImap (Associates.irreducible_mk.mpr hpmap.irreducible),
      ← Associates.prime_pow_dvd_iff_le hmkI (Associates.irreducible_mk.mpr hp.irreducible),
      ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
      Associates.mk_le_mk_iff_dvd]
    exact map_pow_dvd_map_iff_of_ringEquiv e p I n
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

end DedekindDomain

end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

section CommRing

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- Mathlib's transport `equivOfRingEquiv e` of height one primes along a ring isomorphism `e`
pushes the underlying ideal forward: `(equivOfRingEquiv e v).asIdeal = Ideal.map e v.asIdeal`. -/
theorem asIdeal_equivOfRingEquiv (e : R ≃+* R') (v : HeightOneSpectrum R) :
    (equivOfRingEquiv e v).asIdeal = Ideal.map e v.asIdeal := by
  ext x
  -- `equivOfRingEquiv` transports a prime by comapping along `e.symm`, so membership in its ideal
  -- is by definition membership of `e.symm x`, and the two descriptions agree by
  -- `Ideal.symm_apply_mem_of_equiv_iff`.
  change e.symm x ∈ v.asIdeal ↔ x ∈ Ideal.map e v.asIdeal
  exact Ideal.symm_apply_mem_of_equiv_iff

end CommRing

section DedekindDomain

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

/-- **The integer adic valuation transports along a ring isomorphism.** If the height one prime `w`
of `R'` is the image of the height one prime `v` of `R` under `e`, then the `w`-adic valuation of
`e r` is the `v`-adic valuation of `r`. -/
theorem intValuation_ringEquiv (e : R ≃+* R') {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    (hvw : w.asIdeal = Ideal.map e v.asIdeal) (r : R) :
    w.intValuation (e r) = v.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have her : e r ≠ 0 := by simp [hr]
    have hspan : Ideal.span {e r} = Ideal.map e (Ideal.span {r}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [w.intValuation_if_neg her, v.intValuation_if_neg hr, hvw, hspan,
      Ideal.count_factors_map_of_ringEquiv e ((Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime)
        (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hr)]

variable {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
  [IsFractionRing R' K']

/-- The fraction-field adic valuation transports on the image of `R`, which is the building block
for `valuation_ringEquivOfRingEquiv`. -/
theorem valuation_ringEquivOfRingEquiv_algebraMap (e : R ≃+* R') {v : HeightOneSpectrum R}
    {w : HeightOneSpectrum R'} (hvw : w.asIdeal = Ideal.map e v.asIdeal) (r : R) :
    w.valuation K' (IsFractionRing.ringEquivOfRingEquiv e (algebraMap R K r)) =
      v.valuation K (algebraMap R K r) := by
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap e r, valuation_of_algebraMap,
    valuation_of_algebraMap]
  exact intValuation_ringEquiv e hvw r

/-- **The adic valuation of the fraction field transports along a ring isomorphism.** With
`σ = IsFractionRing.ringEquivOfRingEquiv e` the induced isomorphism of fraction fields, and `w` the
image of `v` under `e`, the `w`-adic valuation of `σ f` is the `v`-adic valuation of `f`. This is
the algebraic engine of divisor Galois descent. -/
theorem valuation_ringEquivOfRingEquiv (e : R ≃+* R') {v : HeightOneSpectrum R}
    {w : HeightOneSpectrum R'} (hvw : w.asIdeal = Ideal.map e v.asIdeal) (f : K) :
    w.valuation K' (IsFractionRing.ringEquivOfRingEquiv e f) = v.valuation K f := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  rw [map_div₀, Valuation.map_div, Valuation.map_div,
    valuation_ringEquivOfRingEquiv_algebraMap e hvw a,
    valuation_ringEquivOfRingEquiv_algebraMap e hvw b]

end DedekindDomain

end IsDedekindDomain.HeightOneSpectrum
