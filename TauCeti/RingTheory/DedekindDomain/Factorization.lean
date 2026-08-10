/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Divisibility reading of the multiplicity of a height one prime

Mathlib's `IsDedekindDomain.HeightOneSpectrum` factorization API measures the multiplicity of a
prime `v` in an ideal `J` as `Associates.count (Associates.mk v.asIdeal) (Associates.mk J).factors`
and relates it to valuations, but does not say what that number means as divisibility. This file
supplies the missing reading:

* `IsDedekindDomain.HeightOneSpectrum.le_count_iff_le_pow`: the multiplicity is at least `k`
  exactly when `v ^ k` contains `J`.

That is the form in which multiplicities are compared across a ring extension: one shows the two
ideals contain the same prime powers and concludes the multiplicities agree. The `S`-integer
class-group computation in `TauCeti/RingTheory/DedekindDomain/SInteger/ClassGroup.lean` runs on it,
advancing `TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 (Mordell–Weil), whose
weak-Mordell–Weil argument needs the `S`-class group to be finite.

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

end
