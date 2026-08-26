/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-!
# Primes above a set of primes, and the Selmer group relative to them

Let `R ⊆ B` be Dedekind domains with `B` integral over `R`. For a set `S` of primes of `R`,
`IsDedekindDomain.HeightOneSpectrum.primesAbove R B S` is the set of primes of `B` lying above a
prime in `S`, i.e. whose contraction `HeightOneSpectrum.under R w` lies in `S`. It is finite when
`S` is, and it is the set of primes that the Selmer group of the fraction field of `B` is taken
relative to when the "bad" primes are given downstairs:
`IsDedekindDomain.selmerGroupAbove R B L S n` is Mathlib's `L⟮primesAbove R B S, n⟯`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.primesAbove`: the primes of `B` above a set of primes
  of `R`.
* `IsDedekindDomain.selmerGroupAbove`: the `n`-Selmer group of `L` relative to the primes of `B`
  above `S`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff`: `w` lies above `S` iff
  `HeightOneSpectrum.under R w ∈ S`.
* `IsDedekindDomain.HeightOneSpectrum.primesAbove_finite`: finitely many primes lie above a
  finite set.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (Mordell–Weil): the `2`-descent bounds the
image of the descent map inside a Selmer group taken relative to the bad primes, which are given
downstairs, over the base field, while the group itself lives upstairs, over the étale algebra;
`selmerGroupAbove` is that group and `primesAbove_finite` keeps it finite. Nothing here mentions a
curve.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `DedekindDomain`. The source carries its own
`HeightOneSpectrum.below`; at our Mathlib pin that map is `HeightOneSpectrum.under`, which is
used here instead. The source is written against Lean `v4.32.0`; this is a forward port.
-/

public section

namespace IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
  (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]

namespace HeightOneSpectrum

/-- The primes of `B` lying above a set `S` of primes of `R`. -/
def primesAbove (S : Set (HeightOneSpectrum R)) : Set (HeightOneSpectrum B) :=
  {w | ∃ v ∈ S, v.asIdeal = w.asIdeal.under R}

-- `HeightOneSpectrum` and `primesAbove` need only the ring structure, so the section's
-- Dedekind hypotheses are dropped from the results that do not use them.
omit [IsDedekindDomain R] [IsDedekindDomain B] in
lemma primesAbove_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) :
    primesAbove R B S ⊆ primesAbove R B T :=
  fun _ ⟨v, hv, hva⟩ ↦ ⟨v, hST hv, hva⟩

omit [IsDedekindDomain R] [IsDedekindDomain B] in
@[simp]
lemma primesAbove_empty : primesAbove R B (∅ : Set (HeightOneSpectrum R)) = ∅ := by
  ext w
  simp [primesAbove]

variable [Algebra.IsIntegral R B]

lemma mem_primesAbove_iff (S : Set (HeightOneSpectrum R)) (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ under R w ∈ S := by
  refine ⟨fun ⟨v, hv, hva⟩ ↦ ?_, fun hw ↦ ⟨under R w, hw, rfl⟩⟩
  rwa [show under R w = v from HeightOneSpectrum.ext hva.symm]

/-- Only finitely many primes of `B` lie above a finite set of primes of `R`: each fiber
injects into `Ideal.primesOver`, which is finite for a Dedekind extension. -/
lemma primesAbove_finite [Module.IsTorsionFree R B] {S : Set (HeightOneSpectrum R)}
    (hS : S.Finite) : (primesAbove R B S).Finite := by
  have hsub : primesAbove R B S ⊆
      ⋃ v ∈ S, {w : HeightOneSpectrum B | w.asIdeal ∈ v.asIdeal.primesOver B} :=
    fun w ⟨v, hv, hva⟩ ↦ Set.mem_biUnion hv ⟨w.isPrime, ⟨hva⟩⟩
  refine (hS.biUnion fun v _ ↦ ?_).subset hsub
  have := v.isMaximal
  exact (IsDedekindDomain.primesOver_finite v.asIdeal B).preimage
    (fun a _ b _ hab ↦ HeightOneSpectrum.ext hab)

end HeightOneSpectrum

/-- The `S`-Selmer group of `L`, where `B` is a Dedekind domain with fraction field `L` and `S`
is a set of primes of `R`: the classes of `Lˣ` modulo `n`-th powers whose valuation is divisible
by `n` at every prime of `B` not lying above `S`. -/
def selmerGroupAbove (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) : Subgroup (Lˣ ⧸ (powMonoidHom n : Lˣ →* Lˣ).range) :=
  selmerGroup (R := B) (K := L) (S := HeightOneSpectrum.primesAbove R B S) (n := n)

omit [IsDedekindDomain R] in
lemma mem_selmerGroupAbove_iff (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) (x : Lˣ ⧸ (powMonoidHom n : Lˣ →* Lˣ).range) :
    x ∈ selmerGroupAbove R B L S n ↔
      ∀ w ∉ HeightOneSpectrum.primesAbove R B S, w.valuationOfNeZeroMod n x = 1 :=
  Iff.rfl

end IsDedekindDomain

end
