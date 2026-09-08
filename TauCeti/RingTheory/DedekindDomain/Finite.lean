/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# A normal module-finite algebra is a Dedekind domain

Let `R` be a nontrivial Noetherian ring of Krull dimension at most one, and let `S` be a
module-finite `R`-algebra which is an integrally closed domain. Then `S` is a Dedekind domain: it
is Noetherian because it is module-finite over a Noetherian ring, and of dimension at most one
because it is integral over `R`. So **normality is the only one of the three conditions that has
to be assumed** — the other two are inherited from the base.

Neither inherited half needs `R` to be a domain or integrally closed, so the base is not assumed
Dedekind. `R = F[X]` for a field `F` is the case a curve's coordinate ring uses.

Mathlib's `IsIntegralClosure.isDedekindDomain` and `integralClosure.isDedekindDomain` reach the
same conclusion, but through `IsIntegralClosure C A L`: they describe `C` as *the* integral closure
of `A` inside a finite extension `L` of the fraction field. A caller holding only
`[IsIntegrallyClosed S]` and `[Module.Finite R S]` has no such `L` to name, which is the gap this
fills.

## Main results

* `TauCeti.IsDedekindDomain.of_finite`: a module-finite, integrally closed domain algebra over a
  nontrivial Noetherian base of dimension at most one is a Dedekind domain.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I — normality, Noetherianity
  and dimension one as the three conditions defining a Dedekind domain.

## Provenance

Original work, over Mathlib's `Ring.DimensionLEOne.of_isIntegral` and
`IsNoetherianRing.of_finite`.
-/

public section

namespace TauCeti

/-- **A normal module-finite algebra over a Noetherian base of dimension at most one is a Dedekind
domain.** Only normality of `S` is assumed: Noetherianity is inherited from module-finiteness over
a Noetherian ring, and dimension at most one from integrality over `R`. -/
theorem IsDedekindDomain.of_finite (R : Type*) [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] (S : Type*) [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S] : IsDedekindDomain S :=
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  { IsNoetherianRing.of_finite R S, Ring.DimensionLEOne.of_isIntegral R S,
    ‹IsIntegrallyClosed S› with : IsDedekindDomain S }

end TauCeti

end
