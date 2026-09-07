/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# A finite normalization from a separating polynomial model

Let `A` be a polynomial algebra `F[X]` over a field, `K` its fraction field and `L` a finite
separable extension of `K`. If every element of `A` is integral over a base ring `R` in `L`, then
any integral closure `C` of `R` in `L` is a **finite** `R`-module.

The route is three reductions, each shedding one hypothesis of the previous: a polynomial model is
a Dedekind domain of finite type, so the separable-field case applies; that case replaces `L` by
the integral closure of `A` in it, which is Dedekind with `L` as its fraction field, so the
fraction-field case applies; and there the normalization is an overring of a Dedekind domain
inside its own fraction field, hence integrally closed, and finiteness comes from adjoining the
images of a finite generating set.

## Main result

* `IsIntegralClosure.finite_of_polynomial_model`: finiteness of the integral closure in a finite
  separable extension of the fraction field of a polynomial model.

## Relation to `NormalizationFinite.lean`

That file proves the *Noetherian* statement — Krull–Akizuki — for an integral closure in a finite
extension with **no** separability hypothesis, and says explicitly that the closure need not be a
finite module. This file proves the stronger *module-finiteness* conclusion, and pays for it with
separability of `L / K` together with a polynomial model of `A`. Neither subsumes the other.

## Provenance

Adapted from D. K. Angdinata's `NormalizationFinite.lean`, Apache-2.0, supplied directly by the
author on 2026-09-07, declarations `Subalgebra.isIntegrallyClosed_overring`,
`IsIntegralClosure.isIntegral_trans_common`, `IsIntegralClosure.algebraMap_mem_adjoin_image`,
`IsIntegralClosure.finite_of_fraction_model`, `IsIntegralClosure.finite_of_separable_model` and
`IsIntegralClosure.finite_of_polynomial_model`. That file's header reads
`Authors: David Kurniadi Angdinata`; following this repository's convention for adapted material
the header here names the Tau Ceti contributors and the credit is recorded in this section. The
file as supplied has sha256
`78ad3bd7b9a6cccd4a65c7aa613c268e`
`b588f71118439ae60d83cc33bec56294`.

The file is not yet in AINTLIB (`github.com/CBirkbeck/AINTLIB`, checked at `160e446617a2`), and
`Mathlib.RingTheory.IntegralClosure.NormalizationFinite` — the module path it imports itself
against upstream — does not exist in the pinned Mathlib, so there is nothing to reuse: a compiled
probe reports `Unknown constant IsIntegralClosure.finite_of_polynomial_model`. When Mathlib gains
it, this file and its module path are removed rather than aliased.

The mathematics is unmodified from the source; only the header, this docstring and the import
grouping differ.
-/

noncomputable section

open Polynomial

open scoped nonZeroDivisors

namespace Subalgebra

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- Every overring of a Dedekind domain in its fraction field is integrally closed. -/
private theorem isIntegrallyClosed_overring (C : Subalgebra A K) : IsIntegrallyClosed C := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro q _ hq
  let p : Ideal A := q.comap (algebraMap A C)
  have p_prime : p.IsPrime := hq.isPrime.comap (algebraMap A C)
  let S : Subalgebra C K := Localization.subalgebra.ofField K q.primeCompl
    q.primeCompl_le_nonZeroDivisors
  let T : Subalgebra A K := Localization.subalgebra.ofField K p.primeCompl
    p.primeCompl_le_nonZeroDivisors
  have hTS : T.toSubring ≤ S.toSubring := by
    rintro x ⟨a, s, hs, rfl⟩
    refine ⟨algebraMap A C a, algebraMap A C s, ?_, ?_⟩
    · simpa [p] using hs
    · rfl
  have hS : ∀ x : K, x ∈ S ∨ x⁻¹ ∈ S := by
    intro x
    by_cases hp : p = ⊥
    · left
      apply hTS
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A x
      refine ⟨a, b, ?_, ?_⟩
      · simpa [p, hp, Ideal.primeCompl_bot] using nonZeroDivisors.ne_zero hb
      · simpa [div_eq_mul_inv] using hab.symm
    · exact ((valuationSubringAtPrime K ⟨p, p_prime, hp⟩).mem_or_inv_mem x).imp
        (fun hx ↦ hTS hx) fun hx ↦ hTS hx
  let V : ValuationSubring K := ValuationSubring.ofSubring S.toSubring hS
  exact (inferInstance : IsIntegrallyClosed V).of_equiv
    (IsLocalization.algEquiv q.primeCompl S (Localization.AtPrime q)).toRingEquiv

end Subalgebra

namespace IsIntegralClosure

/-- Integrality transfers through compatible maps from two rings into a common ring. -/
private theorem isIntegral_trans_common {R P L : Type*} [CommRing R] [CommRing P]
    [CommRing L] [Algebra R L] [Algebra P L]
    (hP : ∀ x : P, IsIntegral R (algebraMap P L x)) {x : L}
    (hx : IsIntegral P x) : IsIntegral R x := by
  let S := Algebra.adjoin R (Set.range (algebraMap P L))
  let integral : Algebra.IsIntegral R S := Algebra.IsIntegral.adjoin fun y hy ↦ by
    obtain ⟨z, rfl⟩ := hy
    exact hP z
  let pToS : P →+* S := RingHom.codRestrict (algebraMap P L) S fun z ↦
    Algebra.subset_adjoin ⟨z, rfl⟩
  let pAlgebra : Algebra P S := pToS.toAlgebra
  let scalarTower : IsScalarTower P S L := IsScalarTower.of_algebraMap_eq' rfl
  exact isIntegral_trans (R := R) (A := S) x (hx.tower_top (A := S))

variable {F R A K : Type*} [CommRing F] [CommRing R] [CommRing A] [Field K]
  [Algebra F R] [Algebra F A] [Algebra F K] [Algebra R K] [Algebra A K]
  [IsScalarTower F R K] [IsScalarTower F A K]

private theorem algebraMap_mem_adjoin_image (s : Finset A)
    (hs : Algebra.adjoin F (s : Set A) = ⊤) (x : A) :
    algebraMap A K x ∈ Algebra.adjoin R (algebraMap A K '' (s : Set A)) := by
  let B := Algebra.adjoin R (algebraMap A K '' (s : Set A))
  induction (show x ∈ Algebra.adjoin F (s : Set A) from by simp [hs])
    using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hx)
  | algebraMap x =>
      rw [show algebraMap A K (algebraMap F A x) =
          algebraMap R K (algebraMap F R x) by
        rw [← IsScalarTower.algebraMap_apply F A,
          ← IsScalarTower.algebraMap_apply F R]]
      exact B.algebraMap_mem (algebraMap F R x)
  | add x y _ _ hx hy => simpa only [map_add] using B.add_mem hx hy
  | mul x y _ _ hx hy => simpa only [map_mul] using B.mul_mem hx hy

variable {C : Type*} [IsDedekindDomain A] [IsFractionRing A K]
  [CommRing C] [Algebra R C] [Algebra C K] [IsScalarTower R C K]
  [IsIntegralClosure C R K] [Algebra.FiniteType F A]

include F in
/-- A finite-type fraction-field model integral over the base yields a finite normalization. -/
private theorem finite_of_fraction_model
    (hint : ∀ x : A, IsIntegral R (algebraMap A K x)) : Module.Finite R C := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F A).out
  let B : Subalgebra R K := Algebra.adjoin R (algebraMap A K '' (s : Set A))
  let finiteType : Algebra.FiniteType R B :=
    Algebra.FiniteType.adjoin_of_finite (s.finite_toSet.image _)
  let integral : Algebra.IsIntegral R B := Algebra.IsIntegral.adjoin fun _ hx ↦ by
    obtain ⟨x, -, rfl⟩ := hx
    exact hint x
  let finite : Module.Finite R B := Algebra.IsIntegral.finite
  let D : Subalgebra A K :=
    { carrier := B
      mul_mem' := B.mul_mem
      add_mem' := B.add_mem
      algebraMap_mem' := algebraMap_mem_adjoin_image s hs }
  let integrallyClosedB : IsIntegrallyClosed B := Subalgebra.isIntegrallyClosed_overring D
  let fractionRingB : IsFractionRing B K := inferInstanceAs (IsFractionRing D K)
  let isIntegralClosure : IsIntegralClosure B R K := IsIntegralClosure.of_isIntegrallyClosed B R K
  exact Module.Finite.equiv (IsIntegralClosure.equiv R B K C).toLinearEquiv

end IsIntegralClosure

namespace IsIntegralClosure

variable {F R A K L C : Type*} [CommRing F] [CommRing R] [CommRing A]
  [Field K] [Field L] [CommRing C]
  [Algebra F R] [Algebra F A] [Algebra F L] [Algebra R L]
  [Algebra A K] [Algebra A L] [Algebra K L]
  [IsScalarTower F R L] [IsScalarTower F A L] [IsScalarTower A K L]
  [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsDedekindDomain A] [Algebra.FiniteType F A]
  [Algebra R C] [Algebra C L] [IsScalarTower R C L] [IsIntegralClosure C R L]

include F K in
/-- A finite separable field model integral over the base yields a finite normalization. -/
private theorem finite_of_separable_model
    (hint : ∀ x : A, IsIntegral R (algebraMap A L x)) : Module.Finite R C := by
  let D := integralClosure A L
  let finite : Module.Finite A D := IsIntegralClosure.finite A K L D
  let dedekind : IsDedekindDomain D := IsIntegralClosure.isDedekindDomain A K L D
  let fractionRing : IsFractionRing D L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L D
  let finiteType : Algebra.FiniteType F D :=
    (inferInstance : Algebra.FiniteType F A).trans inferInstance
  exact finite_of_fraction_model (F := F) (A := D) (K := L)
    fun x ↦ isIntegral_trans_common hint x.property

end IsIntegralClosure

@[expose] public section

namespace IsIntegralClosure

variable {F R A K L C : Type*} [Field F] [CommRing R] [CommRing A]
  [Field K] [Field L] [CommRing C]
  [Algebra F R] [Algebra F A] [Algebra F L] [Algebra R L]
  [Algebra A K] [Algebra A L] [Algebra K L]
  [IsScalarTower F R L] [IsScalarTower F A L] [IsScalarTower A K L]
  [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Algebra R C] [Algebra C L] [IsScalarTower R C L] [IsIntegralClosure C R L]

include K in
/-- A separating polynomial model integral over the base yields a finite normalization. -/
theorem finite_of_polynomial_model (e : F[X] ≃ₐ[F] A)
    (hint : ∀ x : A, IsIntegral R (algebraMap A L x)) : Module.Finite R C := by
  let nontrivial : Nontrivial A := e.symm.toRingHom.domain_nontrivial
  let noZeroDivisors : NoZeroDivisors A := Function.Injective.noZeroDivisors e.symm
    e.symm.injective e.symm.map_zero e.symm.map_mul
  let domain : IsDomain A := NoZeroDivisors.to_isDomain A
  let principal : IsPrincipalIdealRing A :=
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  let dedekind : IsDedekindDomain A := inferInstance
  let finiteType : Algebra.FiniteType F A :=
    Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  exact finite_of_separable_model (F := F) (R := R) (A := A) (K := K) (L := L) (C := C) hint

end IsIntegralClosure
