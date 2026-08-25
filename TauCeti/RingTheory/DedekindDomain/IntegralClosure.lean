/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Proof-only: Krull–Akizuki supplies the Noetherian half, and is not named in the statement.
import TauCeti.RingTheory.IntegralClosure.NormalizationFinite
-- Proof-only: the integral closure's own fraction field is built inside the proof.
import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# The integral closure of a Dedekind domain is Dedekind, with no separability

Let `A` be a Dedekind domain with fraction field `K`, let `L` be a finite extension of `K`, and let
`C` be an integral closure of `A` in `L`. Then `C` is again a Dedekind domain. **No separability of
`L / K` is assumed**, so inseparable extensions are covered, and with them the Frobenius isogeny of
a curve over a field of positive characteristic.

Mathlib proves the same statement as `IsIntegralClosure.isDedekindDomain`, but under
`[Algebra.IsSeparable K L]`. Only one of the three conditions defining a Dedekind domain is
responsible for that hypothesis: Mathlib reaches Noetherianity through the trace pairing, which is
nondegenerate exactly in the separable case. Integral closedness and dimension at most one are
already separability-free there. So the whole of the work is to replace that one input by
Krull–Akizuki, `TauCeti.IsIntegralClosure.isNoetherianRing`; the other two components are Mathlib's,
unchanged.

## Main results

* `TauCeti.IsIntegralClosure.isDedekindDomain`: an integral closure of a Dedekind domain in a finite
  extension of its fraction field is a Dedekind domain, with no separability hypothesis.

## Design

**What the trace pairing takes with it.** Mathlib's separable route produces `Module.Finite A C`
along the way (`IsIntegralClosure.finite`), and that by-product genuinely does not survive:
Krull–Akizuki bounds lengths, not ranks, and the integral closure it handles need not be a finite
`A`-module. Only the Dedekind conclusion is recovered here. A caller who also needs finiteness
still needs a normalization-finiteness theorem of Nagata type, which this repository does not have;
`TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/IntermediateRing/Finite.lean` records the same gap
on the isogeny side.

**Why `C` is abstract.** The statement is about any `C` with `[IsIntegralClosure C A L]` rather than
about Mathlib's `integralClosure A L` subalgebra, following the convention of the Krull–Akizuki
theorem it consumes. The consumer that motivates it,
`TauCeti.Isogeny.isDedekindDomain_intermediateRing`, holds a `Subring` of a function field which is
known to be an integral closure but is not that subalgebra; and taking `C` abstractly leaves the
subalgebra case available as the instance `C := integralClosure A L`.

## Provenance

⚠ *mathlib-track*. Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and
isogenies* (`TauCetiRoadmap/EllipticCurves/README.md:1086`), which names
`RingTheory/IntegralClosure/NormalizationFinite` among the supports of D. Angdinata's isogeny
development (`:1096`) and records that the hypothesis inventory of that development is "genuinely
minimal" (`:1097`). Separability is not in that inventory, and this file is what takes it out of
the Dedekind conclusion.

The proof is Mathlib's `IsIntegralClosure.isDedekindDomain`
(`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`) with its Noetherian input replaced: the
dimension component `Ring.DimensionLEOne.of_isIntegral` and the integral-closedness component are
taken from there unchanged, since neither ever used separability. What is not Mathlib's is
`TauCeti.IsIntegralClosure.isNoetherianRing`, proved in
`TauCeti/RingTheory/IntegralClosure/NormalizationFinite.lean`.
-/

public section

namespace TauCeti

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
variable {L : Type*} [Field L] [Algebra A L]

/-- **The integral closure of a Dedekind domain is a Dedekind domain**, for a finite extension `L`
of the fraction field `K` that is not assumed separable.

This is Mathlib's `IsIntegralClosure.isDedekindDomain` with the separability hypothesis removed.
Separability serves only to make the trace pairing nondegenerate and so deliver Noetherianity, and
Krull–Akizuki (`TauCeti.IsIntegralClosure.isNoetherianRing`) delivers that without it. Finiteness
of `C` as an `A`-module, which the separable route yields as a by-product, is *not* available
here. -/
theorem IsIntegralClosure.isDedekindDomain (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L] [Module.Finite K L] (C : Type*) [CommRing C] [IsDomain C]
    [Algebra A C] [Algebra C L] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    IsDedekindDomain C :=
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  { _root_.TauCeti.IsIntegralClosure.isNoetherianRing (A := A) (L := L) K C,
    Ring.DimensionLEOne.of_isIntegral A C,
    (isIntegrallyClosed_iff L).mpr fun {x} hx =>
      ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := A) _ hx),
        IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain C }

end TauCeti
