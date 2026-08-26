/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Transport principles for integral closures and their finiteness

Three general facts that the finiteness of integral closures is assembled from, each stated in
the abstract `IsIntegralClosure` form and independent of the others.

* Descending the base: an integral closure of `A` in `B` is also the integral closure of `R` in
  `B` when `A` is integral over `R` — the converse of Mathlib's `IsIntegralClosure.tower_top`,
  and Stacks, Lemma 10.36.16 (tag 00GQ).
* Descending along an embedding: if the integral closure of `A` in a bigger ring is a finite
  module over the Noetherian ring `A`, so is the integral closure in a ring that embeds into it —
  the "as `R` is Noetherian it suffices to enlarge the field" step that Stacks uses in
  Lemmas 10.161.5, 10.161.12 and 10.161.13.
* Fraction fields: the fraction field of a domain finite over `R` is finite-dimensional over the
  fraction field of `R`, for arbitrary fraction fields (Mathlib states this only for
  `FractionRing R` and `FractionRing S`).

## Main results

* `TauCeti.IsIntegralClosure.tower_bot`: the integral closure of `A` in `B` is the integral
  closure of `R` in `B` when `A` is integral over `R`.
* `TauCeti.IsIntegralClosure.finite_of_injective`: finiteness of an integral closure descends
  along an injective `A`-algebra map of the top rings, over a Noetherian `A`.
* `TauCeti.IsFractionRing.finiteDimensional_of_finite`: `Frac S / Frac R` is finite when `S / R`
  is a finite extension of domains.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`. The statements are Stacks, Lemmas 10.36.16
and 10.36.15(2) (tags 00GQ, 00GP; "Proof. Omitted"), the Noetherian reduction sentence of
Stacks 10.161.12 (tag 032N), and the fraction-field sentence of Stacks 10.161.5 (tag 032I).
-/

public section

-- Skeleton of the normalization-finiteness development: `sorry` is an error under the library's
-- `warningAsError`, so it is downgraded here until the proofs land. Remove with the last `sorry`.
set_option warningAsError false

namespace TauCeti

/-- Source: Stacks, Lemma 10.36.16 (tag 00GQ): "Let `A → B → C` be ring maps. Let `B′` be the
integral closure of `A` in `B`, let `C′` be the integral closure of `B′` in `C`. Then `C′` is
the integral closure of `A` in `C`." Here in the form used by normalization-finiteness: if `C` is
the integral closure of `A` in `B` and `A` is integral over `R`, then `C` is the integral closure
of `R` in `B`. The converse of Mathlib's `IsIntegralClosure.tower_top`. -/
theorem IsIntegralClosure.tower_bot {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra C B] [IsScalarTower R A B]
    [IsIntegralClosure C A B] [Algebra.IsIntegral R A] : IsIntegralClosure C R B := by
  sorry

/-- Source: Stacks, Lemma 10.161.12 (tag 032N), proof: "Choose a finite normal field extension
`M/K` containing `L`. As `R` is Noetherian it suffices to show that the integral closure of `R`
in `M` is finite over `R`." Finiteness of integral closures descends along injective `A`-algebra
maps of the top rings: `C` maps `A`-linearly and injectively into `C'`, and a submodule of a
finite module over a Noetherian ring is finite. -/
theorem IsIntegralClosure.finite_of_injective {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M K' : Type*} [CommRing M] [CommRing K'] [Algebra A M] [Algebra A K'] {C C' : Type*}
    [CommRing C] [CommRing C'] [Algebra A C] [Algebra C M] [IsScalarTower A C M]
    [IsIntegralClosure C A M] [Algebra A C'] [Algebra C' K'] [IsScalarTower A C' K']
    [IsIntegralClosure C' A K'] [Module.Finite A C'] (ι : M →ₐ[A] K')
    (hι : Function.Injective ι) : Module.Finite A C := by
  sorry

/-- Source: Stacks, Lemma 10.161.5 (tag 032I), proof: "Let `M` be a finite field extension of
the fraction field of `S`. Then `M` is also a finite field extension of `K`" (`S` finite over
`R`, `K` the fraction field of `R`). The fraction field of a domain `S` finite and torsion-free
over a domain `R` is finite-dimensional over the fraction field of `R`, for abstract fraction
fields `K` and `L`; Mathlib's instance covers only `FractionRing R` and `FractionRing S`. -/
theorem IsFractionRing.finiteDimensional_of_finite (R S K L : Type*) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S] [Module.Finite R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] :
    FiniteDimensional K L := by
  sorry

end TauCeti
