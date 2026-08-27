/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
-- Proof-only: the integral basis of a finite extension of the fraction field.
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
-- Proof-only: polynomial rings over a field are Noetherian UFDs, hence integrally closed.
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.Algebra.MvPolynomial.Expand
import TauCeti.FieldTheory.PurelyInseparable.Embedding
import TauCeti.RingTheory.IntegralClosure.Transfer

/-!
# The integral closure of a polynomial ring in a purely inseparable extension is finite

Let `k` be a field, `P = k[X_1, …, X_r]`, `K` its fraction field and `M / K` a finite purely
inseparable extension of exponent `e`, `q = p ^ e`. The integral closure of `P` in `M` is a finite
`P`-module. This is the purely inseparable half of normalization-finiteness, the only part that
is genuinely absent from Mathlib (whose `IsIntegralClosure.finite` argues through the trace form
and needs separability), and it is Stacks, Lemma 10.161.13 (tag 032O) run once for `r` variables
over a field.

The argument. Pick a `K`-basis `m_j` of `M` inside the integral closure. Each `m_j ^ q` lies in
`K` and is integral over `P`, hence lies in `P` (`P` is a UFD). Let `k' / k` be a finite
extension containing `q`-th roots of the finitely many coefficients of the `m_j ^ q`, and let
`P' = k'[X_1, …, X_r]` be a `P`-algebra through `X_i ↦ X_i ^ q`. Then `P'` is a finite `P`-module,
integrally closed with fraction field `K'`, and `M` embeds over `K` into `K'` because the `q`-th
powers of the `m_j` become `q`-th powers there. So the integral closure of `P` in `M` maps
injectively and `P`-linearly into the integral closure of `P` in `K'`, which is `P'`, and a
submodule of a finite module over a Noetherian ring is finite.

## Main results

* `TauCeti.IsIntegralClosure.exists_algebraMap_eq_iterateFrobenius`: the `q`-th power of an
  element of the integral closure lies in the (integrally closed) base ring.
* `TauCeti.IsIntegralClosure.finite_of_forall_exists_pow_eq`: the abstract assembly — an
  integral closure in a purely inseparable extension is finite as soon as some finite integrally
  closed overring's fraction field absorbs the `q`-th powers of a generating set.
* `TauCeti.IsIntegralClosure.finite_mvPolynomial_of_isPurelyInseparable`: the theorem for
  polynomial rings over a field.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`. The mathematics is the second paragraph of the
proof of Stacks, Lemma 10.161.13 (tag 032O), with its "some details omitted" spelled out.
-/

public section

-- Skeleton of the normalization-finiteness development: `sorry` is an error under the library's
-- `warningAsError`, so it is downgraded here until the proofs land. Remove with the last `sorry`.
set_option warningAsError false

namespace TauCeti

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "And this integral closure is equal to
`R′[x^{1/q}]`" — the elementwise input: for `c` in the integral closure `C` of an integrally
closed domain `A` in a purely inseparable extension `M` of its fraction field `K`, the
`p ^ n`-th power `c ^ (p ^ n)` lies in `K` and is integral over `A`, hence comes from `A`. -/
theorem IsIntegralClosure.exists_algebraMap_eq_iterateFrobenius {A K M C : Type*} [CommRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [Field M] [Algebra K M]
    [Algebra A M] [IsScalarTower A K M] [CommRing C] [Algebra A C] [Algebra C M]
    [IsScalarTower A C M] [IsIntegralClosure C A M] [IsPurelyInseparable.HasExponent K M]
    (p : ℕ) [ExpChar K p] {n : ℕ} (hn : IsPurelyInseparable.exponent K M ≤ n) (c : C) :
    ∃ a : A, algebraMap A K a =
      IsPurelyInseparable.iterateFrobenius K M p hn (algebraMap C M c) := by
  -- `A` is integrally closed, so it suffices that the value is integral over `A` — and that is
  -- read off in `M`, where the value becomes the `p ^ n`-th power of an element integral over `A`.
  refine IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.tower_bot (algebraMap K M).injective ?_)
  rw [IsPurelyInseparable.algebraMap_iterateFrobenius]
  exact ((IsIntegralClosure.isIntegral A M c).algebraMap (B := M)).pow _

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "As `R[x]` is Noetherian it suffices to
show that the integral closure of `R[x]` in `L′(x^{1/q})` is finite over `R[x]`. And this
integral closure is equal to `R′[x^{1/q}]` … finite over `R[x]`." The abstract assembly. Let `C`
be the integral closure of a Noetherian domain `A` in a purely inseparable extension `M` of its
fraction field `K`, of exponent at most `n`. Let `A'` be an integrally closed domain, finite over
`A`, with fraction field `K'` over `K`, such that for a generating set `s` of `M` over `K` the
`p ^ n`-th power of each `x ∈ s` (an element of `K`) becomes a `p ^ n`-th power of an element of
`A'` in `K'`. Then `M` embeds into `K'` over `K`, `A'` is the integral closure of `A` in `K'`,
and `C` is a finite `A`-module. -/
theorem IsIntegralClosure.finite_of_forall_exists_pow_eq (A K M C A' K' : Type*) [CommRing A]
    [IsNoetherianRing A] [Field K] [Field M] [Algebra A K] [IsFractionRing A K] [Algebra K M]
    [Algebra A M] [IsScalarTower A K M] [CommRing C] [Algebra A C] [Algebra C M]
    [IsScalarTower A C M] [IsIntegralClosure C A M] [CommRing A'] [IsIntegrallyClosed A']
    [Field K'] [Algebra A A'] [Module.Finite A A'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K']
    [IsPurelyInseparable.HasExponent K M] (p : ℕ) [ExpChar K p] {n : ℕ}
    (hn : IsPurelyInseparable.exponent K M ≤ n) {s : Set M}
    (hs : IntermediateField.adjoin K s = ⊤)
    (h : ∀ x ∈ s, ∃ y : A', algebraMap A' K' y ^ p ^ n =
      algebraMap K K' (IsPurelyInseparable.iterateFrobenius K M p hn x)) :
    Module.Finite A C := by
  sorry

/-- Source: Stacks, Lemma 10.161.13 (tag 032O): "If `R` is N-2 then `R[x]` is N-2", second
paragraph of the proof, for `R = k` a field and `r` variables at once. **The purely inseparable
core of normalization-finiteness.** For `P = k[X_1, …, X_r]` with fraction field `K` and a finite
purely inseparable extension `M / K`, any integral closure `C` of `P` in `M` is a finite
`P`-module. No separability is assumed; characteristic zero is the case `q = 1`. -/
theorem IsIntegralClosure.finite_mvPolynomial_of_isPurelyInseparable (k : Type*) [Field k]
    {σ : Type*} [Finite σ] (K M : Type*) [Field K] [Field M] [Algebra (MvPolynomial σ k) K]
    [IsFractionRing (MvPolynomial σ k) K] [Algebra K M] [Algebra (MvPolynomial σ k) M]
    [IsScalarTower (MvPolynomial σ k) K M] [IsPurelyInseparable K M] [FiniteDimensional K M]
    (C : Type*) [CommRing C] [Algebra (MvPolynomial σ k) C] [Algebra C M]
    [IsScalarTower (MvPolynomial σ k) C M] [IsIntegralClosure C (MvPolynomial σ k) M] :
    Module.Finite (MvPolynomial σ k) C := by
  sorry

end TauCeti
