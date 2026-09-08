/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# A normal module-finite algebra over a Dedekind domain is Dedekind

Let `R` be a Dedekind domain and `S` a module-finite `R`-algebra which is an integrally closed
domain. Then `S` is again a Dedekind domain: it is Noetherian because it is module-finite over a
Noetherian ring, and of dimension at most one because it is integral over `R`. So **normality is
the only one of the three conditions that has to be assumed** — the other two are inherited.

Mathlib's `IsIntegralClosure.isDedekindDomain` and `integralClosure.isDedekindDomain` reach the
same conclusion, but through `IsIntegralClosure C A L`: they describe `C` as *the* integral closure
of `A` inside a finite extension `L` of the fraction field. A caller holding only
`[IsIntegrallyClosed S]` and `[Module.Finite R S]` has no such `L` to name, which is the gap this
fills.

## Main results

* `TauCeti.IsDedekindDomain.of_moduleFinite`: a module-finite, integrally closed domain algebra
  over a Dedekind domain is a Dedekind domain.

## Provenance

Original work. The proof is the dimension and Noetherian components of Mathlib's
`IsIntegralClosure.isDedekindDomain` (`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`)
recombined for hypotheses that do not mention an ambient field: `Ring.DimensionLEOne.of_isIntegral`
supplies the dimension and `IsNoetherianRing.of_finite` the Noetherian condition, neither of which
uses the integral-closure description.
-/

public section

namespace TauCeti

/-- **A normal module-finite algebra over a Dedekind domain is a Dedekind domain.** Only normality
is assumed: Noetherianity comes from module-finiteness over a Noetherian ring, and dimension at
most one from integrality over `R`. -/
theorem IsDedekindDomain.of_moduleFinite (R : Type*) [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S]
    [Module.Finite R S] : IsDedekindDomain S :=
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  { IsNoetherianRing.of_finite R S, Ring.DimensionLEOne.of_isIntegral R S,
    ‹IsIntegrallyClosed S› with : IsDedekindDomain S }

end TauCeti

end
