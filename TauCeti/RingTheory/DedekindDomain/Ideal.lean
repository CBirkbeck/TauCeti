/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Complements on the height one spectrum of a Dedekind domain

A single fact about distinct height-one primes of a Dedekind domain, complementing
`Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`: distinct height-one primes are
incomparable, so each contains an element the other does not. This is what separates the
valuations at two primes, and it is consumed by
`TauCeti/RingTheory/DedekindDomain/SInteger.lean`.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Distinct height one primes are incomparable: a height one prime is not contained in any
other one, since both are maximal. -/
lemma exists_mem_asIdeal_notMem_asIdeal {v w : HeightOneSpectrum R} (h : w ≠ v) :
    ∃ a ∈ v.asIdeal, a ∉ w.asIdeal := by
  by_contra! hc
  exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)

end IsDedekindDomain.HeightOneSpectrum

end
