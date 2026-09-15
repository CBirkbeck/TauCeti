/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The primes of an intermediate field that Chebotarev discards

Fix an extension `L / K` of number fields and a further number field `E` over `K` — in the
Chebotarev argument `E` is the field fixed by a cyclic subgroup of `Gal(L/K)`, but nothing here
needs that. Counting primes of `E` by their relative Frobenius has to set aside a finite set of
primes, and this file names that set: the primes of `𝓞 E` lying over a prime of `𝓞 K` that
ramifies in `L`.

## Main definitions

* `NumberField.Chebotarev.exceptionalPrimes`: the finite set of height-one primes of `𝓞 E`
  lying over `ramifiedPrimes K L`.

## Main results

* `NumberField.Chebotarev.mem_exceptionalPrimes_iff`: the defining condition for membership.

## Why the primes ramifying in `L / E` are the wrong set

The tempting smaller set is `ramifiedPrimes E L`, the primes of `E` that ramify in `L`. It does
not serve, and the difference is not an edge case: a prime `𝔓` of `E` can be unramified in
`L / E` while the prime `𝔭` of `K` below it ramifies in `L / K`. Then `𝔓` carries a relative
Frobenius and `𝔭` carries no absolute one, so `𝔓` survives into the relative fibre while lying
over no prime the absolute count admits, and the two sides stop matching.

The roadmap's witness is `K = ℚ` and `L = ℚ(∛2, ζ₃)`, where `Gal(L/K) ≅ S₃`; take `σ` a
transposition, so `E = ℚ(∛2)`, and `p = 2`. The inertia group at `2` is the cyclic group of
order three, giving `e(Q/2) = 3` but `e(Q/𝔓) = 1`, with the whole ramification `e(𝔓/2) = 3`
happening below `E`. So `𝔓 ∉ ramifiedPrimes E L` and yet `2 ∈ ramifiedPrimes K L`.

Hence the condition is imposed on the prime *below* `𝔓`, and `L` stays in the statement even
though the primes live in `E`.

## References

Adapted from `ramifiedBelow_finite` in `CebotarevDensity/FixedFieldDensity.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) on branch `development` at commit
`8575c9df1ae0a61120ab5c964c7911414254bec7`. There it is a `private` finiteness statement about a
`Set (Ideal (𝓞 E))` supplied as a variable together with a defining equation, specialised to
`E = IntermediateField.fixedField (Subgroup.zpowers σ)`, and used once, inline, to discard a tail
of a zeta sum. The set is never named, never packaged as a `Finset`, and its membership condition
is never stated.

The source proves finiteness inline, by covering the set with the fibres of the contraction. That
argument is not repeated here: `IsDedekindDomain.HeightOneSpectrum.primesAbove_finite` already
makes it, for an arbitrary finite set of primes downstairs, and this file only supplies
`ramifiedPrimes K L` as that set.
-/

public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable (K L E : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field E] [NumberField E] [Algebra K E]

/-- **The primes of `E` that Chebotarev discards.** The height-one primes of `𝓞 E` lying over a
prime of `𝓞 K` that ramifies in `L`, cut out of `HeightOneSpectrum.primesAbove` by
`HeightOneSpectrum.primesAbove_finite`.

The condition is on the prime of `K` below, not on ramification in `L / E`; the module docstring
has the witness separating the two. -/
noncomputable def exceptionalPrimes : Finset (HeightOneSpectrum (𝓞 E)) :=
  (HeightOneSpectrum.primesAbove_finite (𝓞 K) (𝓞 E)
    (ramifiedPrimes K L).finite_toSet).toFinset

variable {K L E}

/-- The defining condition for membership in `exceptionalPrimes`: `𝔓` lies over a prime of `𝓞 K`
that ramifies in `L`. -/
@[simp]
theorem mem_exceptionalPrimes_iff (𝔓 : HeightOneSpectrum (𝓞 E)) : 𝔓 ∈ exceptionalPrimes K L E ↔
    𝔓.under (𝓞 K) ∈ ramifiedPrimes K L :=
  (Set.Finite.mem_toFinset _).trans (HeightOneSpectrum.mem_primesAbove_iff _ _ _ _)

end NumberField.Chebotarev
