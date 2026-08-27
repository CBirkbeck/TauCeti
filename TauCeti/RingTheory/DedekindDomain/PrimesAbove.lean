/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
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

* `IsDedekindDomain.HeightOneSpectrum.comapOfNeBot`: the contraction of a height-one prime along
  an arbitrary ring homomorphism, given that the contraction is nonzero. It generalises Mathlib's
  `HeightOneSpectrum.comap`, which derives that hypothesis from surjectivity; the maps needed here
  are embeddings into completions, which are neither surjective nor integral.
* `IsDedekindDomain.HeightOneSpectrum.primesAbove`: the primes of `B` above a set of primes
  of `R`, as a preimage under `HeightOneSpectrum.under`.
* `IsDedekindDomain.selmerGroupAbove`: the `n`-Selmer group of `L` relative to the primes of `B`
  above `S`.

## Main results

* `Ideal.comap_ne_bot_of_comap_comap_ne_bot`: a contraction is nonzero once its further
  contraction along an injective map is, which is how the hypothesis of `comapOfNeBot` is
  discharged in practice.
* `IsDedekindDomain.HeightOneSpectrum.comap_maximalIdeal_adicCompletionIntegers`: the maximal
  ideal of the integers of the `v`-adic completion contracts to `v`.
* `IsDedekindDomain.HeightOneSpectrum.liesOver_under`: the `LiesOver` instance relating a prime
  to its contraction, which the `under`-indexed results downstream need.
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
used here instead.

`comapOfNeBot`, `comap_maximalIdeal_adicCompletionIntegers` and
`Ideal.comap_ne_bot_of_comap_comap_ne_bot` are adapted from that source's
`EllipticCurves/Mathlib/Basic.lean`, lines 539, 594 and 270 respectively. They are shared
substrate rather than part of any one rung: the semilocal comparison, the finiteness of the
`2`-Selmer group, and the local image counts all contract primes of a local field factor back to
the base, and all three consume these.

The source is written against Lean `v4.32.0`; this is a forward port.
-/

public section

/-- An ideal contraction is nonzero as soon as its further contraction along an injective ring
homomorphism is nonzero.

Stated here because it is what supplies the nonvanishing hypothesis of
`IsDedekindDomain.HeightOneSpectrum.comapOfNeBot` below at its use sites: one contracts a prime of
a local factor all the way down to the base, where nonvanishing is known, and reads the
intermediate step off from that. -/
lemma Ideal.comap_ne_bot_of_comap_comap_ne_bot {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {ρ : R →+* S} {φ : S →+* T} (hρ : Function.Injective ρ) {I : Ideal T}
    (h : (I.comap φ).comap ρ ≠ ⊥) : I.comap φ ≠ ⊥ := fun h0 ↦
  h (by
    rw [h0, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot ρ).mp hρ])

namespace IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
  (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B] [Algebra.IsIntegral R B]

namespace HeightOneSpectrum

/-- A height one prime of `B` lies over its own contraction to `R`.

Mathlib's `Ideal.over_under` is this statement for `Ideal.under`, but instance search does not see
through the `HeightOneSpectrum.asIdeal` projection to reach it, so it is registered here. Results
stated at `under R w` and consuming a `LiesOver` hypothesis — `HeightOneSpectrum.valuation_liesOver`
is the one this file exists to feed — do not fire without it. -/
instance liesOver_under (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (under R w).asIdeal :=
  ⟨rfl⟩

section Comap

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]

/-- The height-one prime of `B` obtained by contracting a height-one prime of `C` along a ring
homomorphism `ψ : B →+* C`, given that the contraction is nonzero.

Mathlib's `IsDedekindDomain.HeightOneSpectrum.comap` is the same construction, but it asks for `ψ`
to be **surjective** and derives the `ne_bot` field from that. `comapOfNeBot` **generalises** it:
the surjective case is recovered by supplying `(Ideal.eq_bot_of_comap_eq_bot' hf).mt w.ne_bot`, and
only the converse fails.

The generality is needed because the maps contracted along here are embeddings into completions —
`R → v.adicCompletionIntegers K` — which are neither surjective, so Mathlib's `comap` does not
apply, nor integral `Algebra` maps, so `HeightOneSpectrum.under` does not either. (`ℤ → ℤ_p` is
flat, not integral.) The `ne_bot` hypothesis has to be supplied by hand.

Not `@[simps]`: the generated `asIdeal` projection is proved by `rfl`, and a bare `rfl` proof of a
statement exported from this module would require `comapOfNeBot` and its field proofs to be
exposed downstream. The projection is written out below with the parenthesised `(rfl)` instead,
which elaborates here where the definition is visible. -/
def comapOfNeBot (ψ : B →+* C) (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    HeightOneSpectrum B where
  asIdeal := w.asIdeal.comap ψ
  isPrime := w.isPrime.comap ψ
  ne_bot := hne

omit [IsDedekindDomain B] [IsDedekindDomain C] in
/-- The underlying ideal of `comapOfNeBot` is the contracted ideal.

The `IsDedekindDomain` instances are needed to *state* this — they are part of what
`HeightOneSpectrum` means here — but the proof erases them, so they are omitted rather than
suppressed with a linter option. -/
@[simp]
lemma comapOfNeBot_asIdeal (ψ : B →+* C) (w : HeightOneSpectrum C)
    (hne : w.asIdeal.comap ψ ≠ ⊥) :
    (comapOfNeBot ψ w hne).asIdeal = w.asIdeal.comap ψ :=
  (rfl)

end Comap

section AdicCompletion

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The maximal ideal of the ring of integers of the completion of `K` at `v` contracts to `v`
itself. This is what identifies the prime obtained by `comapOfNeBot` from a completion with the
prime one started from. -/
theorem comap_maximalIdeal_adicCompletionIntegers (v : HeightOneSpectrum R) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).comap
      (algebraMap R (v.adicCompletionIntegers K)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← valuation_lt_one_iff_mem (K := K)]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))))).trans ?_
  rw [show ((algebraMap R (v.adicCompletionIntegers K) x : v.adicCompletionIntegers K) :
    v.adicCompletion K) = ((algebraMap R K x : K) : v.adicCompletion K) from rfl,
    valuedAdicCompletion_eq_valuation']

end AdicCompletion

/-- The primes of `B` lying above a set `S` of primes of `R`: the preimage of `S` under the
contraction `HeightOneSpectrum.under R`. -/
def primesAbove (S : Set (HeightOneSpectrum R)) : Set (HeightOneSpectrum B) :=
  under R ⁻¹' S

/-- A prime of `B` lies above `S` exactly when its contraction to `R` lies in `S`. -/
@[simp]
lemma mem_primesAbove_iff (S : Set (HeightOneSpectrum R)) (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ under R w ∈ S := Iff.rfl

lemma primesAbove_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) :
    primesAbove R B S ⊆ primesAbove R B T :=
  Set.preimage_mono hST

@[simp]
lemma primesAbove_empty : primesAbove R B (∅ : Set (HeightOneSpectrum R)) = ∅ :=
  Set.preimage_empty

/-- Only finitely many primes of `B` lie above a finite set of primes of `R`: each fiber
injects into `Ideal.primesOver`, which is finite for a Dedekind extension. -/
lemma primesAbove_finite [Module.IsTorsionFree R B] {S : Set (HeightOneSpectrum R)}
    (hS : S.Finite) : (primesAbove R B S).Finite := by
  have hsub : primesAbove R B S ⊆
      ⋃ v ∈ S, {w : HeightOneSpectrum B | w.asIdeal ∈ v.asIdeal.primesOver B} :=
    fun w hw ↦ Set.mem_biUnion hw ⟨w.isPrime, ⟨rfl⟩⟩
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

/-- `selmerGroupAbove` is the ordinary Selmer group taken over the primes above `S`.

The definition says exactly this, but `selmerGroupAbove` is not `@[expose]`, so a downstream
module cannot see it; this lemma is how such a module rewrites between the two spellings — in
particular to reach `IsDedekindDomain.selmerGroupPi` and `selmerGroupOfEquiv`, which are stated
in terms of `selmerGroup`.

Proved by the parenthesised `(rfl)`: the definition is visible here, whereas a bare `rfl` proof of
an exported statement would ask for `selmerGroupAbove` to be exposed downstream. -/
lemma selmerGroupAbove_def (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) :
    selmerGroupAbove R B L S n =
      selmerGroup (R := B) (K := L) (S := HeightOneSpectrum.primesAbove R B S) (n := n) :=
  (rfl)

/-- A class of units lies in the Selmer group relative to `S` exactly when its
`valuationOfNeZeroMod n` is trivial at every prime of `B` not lying above `S`, i.e. `n` divides
the `w`-adic valuation there. -/
@[simp]
lemma mem_selmerGroupAbove_iff (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) (x : Lˣ ⧸ (powMonoidHom n : Lˣ →* Lˣ).range) :
    x ∈ selmerGroupAbove R B L S n ↔
      ∀ w ∉ HeightOneSpectrum.primesAbove R B S, w.valuationOfNeZeroMod n x = 1 :=
  Iff.rfl

end IsDedekindDomain

end
