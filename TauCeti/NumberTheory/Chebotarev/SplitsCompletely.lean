/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
public import TauCeti.NumberTheory.NumberField.SplitsCompletely

/-!
# The completely split primes as the identity Artin fibre

Let `L / K` be a finite Galois extension of number fields. Among the fibres of the Artin class
studied in `TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet`, the fibre of the identity class
`1` is distinguished: it consists exactly of the primes of `𝓞 K` that split completely in `L`.

Three readings of membership in `frobeniusPrimeSet K L 1` are recorded for a prime `𝔭` that is
unramified in `L`. The residue degree `f(Q/𝔭)` is `1` at one — hence, since `L / K` is Galois, at
every — prime `Q` of `𝓞 L` above `𝔭`; the ring `𝓞 L` has the full complement of `[L : K]` primes
above `𝔭`; and the identity of `Gal(L/K)` is an arithmetic Frobenius at some prime above `𝔭`.

The unramifiedness hypothesis is not needed in the set-level form: a full complement of primes
above `𝔭` already forces the ramification index at every prime above `𝔭` to be `1`, hence forces
`𝔭` to be unramified. So `frobeniusPrimeSet K L 1` is the set of completely split primes on the
nose, with no finite exceptional set to discard.

## Main results

* `NumberField.isUnramifiedAt_of_ncard_primesOver_eq_finrank`: a full complement of `[L : K]`
  primes above `𝔭` makes every prime of `𝓞 L` above `𝔭` unramified.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one`: for `𝔭` unramified
  in `L`, membership in the identity fibre is residue degree one at a prime above `𝔭`.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank`: the same
  membership, read as a count of the primes above `𝔭`.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_one_iff_exists_isArithFrobAt_one`: the same
  membership, read as the identity of `Gal(L/K)` being an arithmetic Frobenius above `𝔭`.
* `NumberField.Chebotarev.inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one`: a member of the
  identity fibre has residue degree one at *every* prime above it.
* `NumberField.Chebotarev.frobeniusPrimeSet_one_eq`: the identity fibre, as a set, is the
  unramified primes with a full complement of primes above them.
* `NumberField.Chebotarev.frobeniusPrimeSet_one_eq_setOf_ncard_primesOver_eq_finrank`: the same
  set equality with the unramifiedness conjunct dropped.
* `NumberField.Chebotarev.frobeniusPrimeSet_one_subset_frobeniusPrimeSet_one`: a prime splitting
  completely in `L` splits completely in every Galois subextension `M` of `L / K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, where the Frobenius at an unramified
  prime is trivial exactly when that prime splits completely.

The identity fibre is Layer 2 of `TauCetiRoadmap/Chebotarev/README.md`, serving Layer 10
("Derive, rather than reprove, the density of split-completely primes") and Layer 14.
-/

public section

open Ideal
open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **A full complement of primes forces unramifiedness.** If `𝓞 L` has `[L : K]` primes above a
maximal ideal `𝔭` of `𝓞 K`, then every prime `Q` of `𝓞 L` above `𝔭` is unramified over `𝓞 K`.

This is the fundamental identity `∑ e f = [L : K]` read for its ramification content rather than
its residue content: with `[L : K]` summands, each already equal to at least `1`, every `e` is
forced to `1`, and for number rings `e = 1` is unramifiedness. -/
theorem isUnramifiedAt_of_ncard_primesOver_eq_finrank (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hsplit : (𝔭.primesOver (𝓞 L)).ncard = Module.finrank K L)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭] :
    Algebra.IsUnramifiedAt (𝓞 K) Q := by
  -- Read the common ramification index of the Galois extension off the prime count, then
  -- transport it to `Q` and convert `e = 1` into unramifiedness.
  rw [← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭 Q (L ≃ₐ[K] L)]
  exact ((ncard_primesOver_eq_finrank_iff_of_isGalois K L 𝔭).mp hsplit).1

namespace Chebotarev

/-- **The identity fibre is residue degree one.** For `𝔭` unramified in `L` and `Q` a prime of
`𝓞 L` above `𝔭`, the prime `𝔭` carries the identity Artin class exactly when `f(Q/𝔭) = 1`.

The residue degree is common to all primes above `𝔭`, so the choice of `Q` is immaterial; see
`inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one`. -/
theorem mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    𝔭 ∈ frobeniusPrimeSet K L 1 ↔ Q.inertiaDeg (𝓞 K) = 1 := by
  rw [mem_frobeniusPrimeSet_iff_artinSymbol_eq hur,
    artinSymbol_eq_one_iff_inertiaDeg_eq_one 𝔭.asIdeal hur Q]

/-- **The identity fibre is complete splitting.** For `𝔭` unramified in `L`, the prime `𝔭`
carries the identity Artin class exactly when `𝓞 L` has `[L : K]` primes above `𝔭`. -/
theorem mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    𝔭 ∈ frobeniusPrimeSet K L 1 ↔
      (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  rw [mem_frobeniusPrimeSet_iff_artinSymbol_eq hur,
    artinSymbol_eq_one_iff_ncard_primesOver_eq_finrank 𝔭.asIdeal hur]

/-- **The identity fibre is a trivial Frobenius.** For `𝔭` unramified in `L`, the prime `𝔭`
carries the identity Artin class exactly when the identity of `Gal(L/K)` is an arithmetic
Frobenius at some prime of `𝓞 L` above `𝔭`. -/
theorem mem_frobeniusPrimeSet_one_iff_exists_isArithFrobAt_one {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    𝔭 ∈ frobeniusPrimeSet K L 1 ↔
      ∃ Q : 𝔭.asIdeal.primesOver (𝓞 L), IsArithFrobAt (𝓞 K) (1 : L ≃ₐ[K] L) Q.1 := by
  -- The identity class is the class of the identity element, so this is the general
  -- representative-wise description of a fibre, instantiated at `σ = 1`.
  rw [ConjClasses.one_eq_mk_one, mem_frobeniusPrimeSet_mk_iff_exists_isArithFrobAt hur]

/-- **Residue degree one at every prime above.** A member of the identity fibre has residue
degree `1` at each prime of `𝓞 L` lying over it, not merely at one of them. -/
theorem inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h : 𝔭 ∈ frobeniusPrimeSet K L 1) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    Q.inertiaDeg (𝓞 K) = 1 :=
  (mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one
    (fun Q _ _ ↦ isUnramifiedAt_of_mem_frobeniusPrimeSet h Q) Q).mp h

/-- **The identity fibre, as a set.** `frobeniusPrimeSet K L 1` is the set of height-one primes
of `𝓞 K` that avoid `ramifiedPrimes K L` and have the full complement of `[L : K]` primes of
`𝓞 L` above them. -/
theorem frobeniusPrimeSet_one_eq :
    frobeniusPrimeSet K L 1 =
      {𝔭 | 𝔭 ∉ ramifiedPrimes K L ∧
        (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L} := by
  ext 𝔭
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    -- Membership already carries an unramifiedness proof; both conjuncts read off it.
    obtain ⟨hur, -⟩ := mem_frobeniusPrimeSet_iff.mp h
    exact ⟨fun hmem ↦ (mem_ramifiedPrimes_iff 𝔭).mp hmem hur,
      (mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank hur).mp h⟩
  · rintro ⟨hnr, hcard⟩
    -- Outside `ramifiedPrimes` the double negation in `mem_ramifiedPrimes_iff` collapses.
    rw [mem_ramifiedPrimes_iff, not_not] at hnr
    exact (mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank hnr).mpr hcard

/-- **The identity fibre is exactly the completely split primes.** The unramifiedness conjunct
of `frobeniusPrimeSet_one_eq` is redundant: a height-one prime of `𝓞 K` carries the identity
Artin class in `L` if and only if `𝓞 L` has `[L : K]` primes above it.

Complete splitting is therefore a fibre of the Artin class with no exceptional set attached, so
a density statement for the fibre is a density statement for the completely split primes. -/
theorem frobeniusPrimeSet_one_eq_setOf_ncard_primesOver_eq_finrank :
    frobeniusPrimeSet K L 1 =
      {𝔭 | (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L} := by
  rw [frobeniusPrimeSet_one_eq]
  ext 𝔭
  simp only [Set.mem_ofPred_eq, and_iff_right_iff_imp]
  intro hcard
  rw [mem_ramifiedPrimes_iff, not_not]
  exact isUnramifiedAt_of_ncard_primesOver_eq_finrank 𝔭.asIdeal hcard

section RestrictNormal

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]
  [IsGalois K M]

/-- **Complete splitting descends to Galois subextensions.** For a tower `L / M / K` with `M / K`
Galois, a prime of `𝓞 K` that splits completely in `L` splits completely in `M`.

This is `frobeniusPrimeSet_subset_map_restrictNormalHom` at the identity class, which restriction
preserves because it is a monoid homomorphism. -/
theorem frobeniusPrimeSet_one_subset_frobeniusPrimeSet_one :
    frobeniusPrimeSet K L 1 ⊆ frobeniusPrimeSet K M 1 := by
  -- `ConjClasses.map` of a monoid hom sends the identity class to the identity class; computed
  -- on the representative `1`, where `map_mk` reduces it to `map_one` in the target group.
  have hone : ConjClasses.map (AlgEquiv.restrictNormalHom M)
      (1 : ConjClasses (L ≃ₐ[K] L)) = 1 := by
    rw [ConjClasses.one_eq_mk_one, ConjClasses.map_mk, _root_.map_one,
      ← ConjClasses.one_eq_mk_one]
  rw [← hone]
  exact frobeniusPrimeSet_subset_map_restrictNormalHom 1

end RestrictNormal

end Chebotarev

end NumberField
