/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import TauCeti.RingTheory.ClassGroup.Basic

/-!
# Principal powers of a height one prime, and the valuations of a generator

Over a Dedekind domain no height one prime need be principal, but a positive power of one is as
soon as its class `[v]` has finite order `m` in the class group: `[v] ^ m = 1` says exactly that
`v ^ m` is principal. A finite class group is the usual source of that hypothesis, but only the
single class `[v]` is at stake. This file records that fact together with its companion, which is
what makes the generator useful: a generator of `v ^ m` is a unit at every height one prime other
than `v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.exists_pow_eq_span`: if the class of `v` has finite order,
  some positive power of `v` is `Ideal.span {π}` for a nonzero `π : R`.
* `IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_eq_one_of_pow_le_span`: if `π`
  divides `v.asIdeal ^ n`, then `w.valuation K (algebraMap R K π) = 1` for every height one
  prime `w ≠ v`.

Together these say that a principal power of `v` supplies an element whose divisor is supported
at `v` alone. That is the substrate for the rank half of Dirichlet's `S`-unit theorem: it is what
exhibits, for each `v ∈ S`, an `S`-unit whose valuation vector is a nonzero multiple of the
standard basis vector at `v`, and hence what makes the range of the `S`-unit logarithm full rank.

## Implementation notes

`exists_pow_eq_span` asks only that the single class `[v]` have finite order, not that the whole
class group be finite: all the proof takes from the hypothesis is one positive `m` with
`[v] ^ m = 1`, which is `IsOfFinOrder.exists_pow_eq_one`. A caller carrying
`[Finite (ClassGroup R)]` supplies the hypothesis as `isOfFinOrder_of_finite _`, so no separate
finite-class-group form is stated here. Nothing weaker will do either: a nonzero `π` with
`v.asIdeal ^ m = Ideal.span {π}` and `0 < m` forces `[v] ^ m = 1`, so finite order of `[v]` is
necessary as well as sufficient.

The second result needs no class hypothesis at all. It is proved by reducing
`w.valuation K (algebraMap R K π) = 1` to `π ∉ w.asIdeal` through Mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem`, then using that a prime
containing `v ^ n` contains `v`, and `v` is maximal.

It also asks only for the containment `v.asIdeal ^ n ≤ Ideal.span {π}` — `π` divides `v ^ n` —
rather than the equality a principal power gives. The proof uses the containment in one direction
only, and the weaker hypothesis is the honest statement of what makes `π` a `w`-adic unit: its
ideal support is contained in `{v}`.

Passing from `[v] ^ m` to the class of `v.asIdeal ^ m` is Mathlib's `SubmonoidClass.mk_pow`,
which is exactly the coercion `(⟨I, hI⟩ : (Ideal R)⁰) ^ m = ⟨I ^ m, _⟩`; Mathlib's own
`Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime` takes the same step the same way.

The exponent is existentially quantified rather than named as `orderOf v.classGroupMk`, because no
consumer so far needs the exponent to be the order: what is used is only that it is positive.
Leaving it existential also keeps the conclusion free of the `ClassGroup` vocabulary that the
hypothesis alone mentions, and lets the proof read the exponent straight off the hypothesis.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/FractionalIdeal.lean`
and `EllipticCurves/Mathlib/Basic.lean` at the roadmap's pin `66889eada51a`, Apache 2.0, by
Michael Stoll); following this repository's convention for adapted material, the upstream
authorship is credited here rather than in the copyright header. Three deliberate departures from
the source: `exists_pow_eq_span` weakens the source's `[Finite (ClassGroup R)]` to finite order of
the single class `[v]`, and reaches the class of `v.asIdeal ^ m` through this repository's
`classGroupMk_eq_mk0` and Mathlib's `SubmonoidClass.mk_pow` instead of an inline `Subtype.ext`
step; and the valuation lemma is stated over the containment rather than the equality.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- If the class of the height one prime `v` has finite order, then some positive power of `v` is
principal, with a nonzero generator. When `ClassGroup R` is finite, pass
`isOfFinOrder_of_finite _` for the hypothesis. -/
lemma exists_pow_eq_span (v : HeightOneSpectrum R) (hv : IsOfFinOrder v.classGroupMk) :
    ∃ (n : ℕ) (π : R), 0 < n ∧ π ≠ 0 ∧ v.asIdeal ^ n = Ideal.span {π} := by
  obtain ⟨m, hm, h1⟩ := hv.exists_pow_eq_one
  rw [classGroupMk_eq_mk0, ← map_pow, SubmonoidClass.mk_pow] at h1
  obtain ⟨π, hπ⟩ := (ClassGroup.mk0_eq_one_iff _).mp h1
  rw [Ideal.submodule_span_eq] at hπ
  exact ⟨m, π, hm, fun h ↦ pow_ne_zero _ v.ne_bot (hπ.trans (by simp [h])), hπ⟩

/-- If `π` divides a power of the height one prime `v` — that is, `v.asIdeal ^ n` is contained
in `Ideal.span {π}` — then `π` is a unit for the `w`-adic valuation at every height one prime
`w ≠ v`. Containment is the weakest hypothesis the proof needs; `exists_pow_eq_span` supplies the
equality, so a caller holding one passes `h.le`. -/
lemma valuation_algebraMap_eq_one_of_pow_le_span {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {v w : HeightOneSpectrum R} (hne : w ≠ v) {n : ℕ} {π : R}
    (h : v.asIdeal ^ n ≤ Ideal.span {π}) : w.valuation K (algebraMap R K π) = 1 := by
  refine w.valuation_eq_one_iff_notMem.mpr fun hmem ↦ hne (HeightOneSpectrum.ext ?_).symm
  refine v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.IsPrime.le_of_pow_le (n := n) ?_)
  exact h.trans (by rwa [Ideal.span_le, Set.singleton_subset_iff])

end IsDedekindDomain.HeightOneSpectrum
