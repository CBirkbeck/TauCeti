/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Transport principles for integral closures and their finiteness

Three general facts that the finiteness of integral closures is assembled from, each stated in
an abstract typeclass form — `IsIntegralClosure` for the first two, `IsFractionRing` for the
third — and independent of the others.

* Descending the base: an integral closure of `A` in `B` is also the integral closure of `R` in
  `B` when `A` is integral over `R` — the converse of Mathlib's `IsIntegralClosure.tower_top`,
  and Stacks, Lemma 10.36.16 (tag 00GQ).
* Descending along an embedding: if the integral closure of `A` in a bigger ring is a finite
  module over the Noetherian ring `A`, so is the integral closure in a ring that embeds into it —
  the "as `R` is Noetherian it suffices to enlarge the field" step that Stacks uses in
  Lemmas 10.161.5, 10.161.12 and 10.161.13.
* Fraction fields: a fraction field of a ring `S` finite over `R` is finite-dimensional over any
  intermediate field `K` with `R → K → L` (Mathlib states this only for the concrete
  `FractionRing R` and `FractionRing S`).

## Main results

* `TauCeti.IsIntegralClosure.tower_bot`: the integral closure of `A` in `B` is the integral
  closure of `R` in `B` when `A` is integral over `R`.
* `TauCeti.IsIntegralClosure.finite_of_injective`: finiteness of an integral closure descends
  along an injective `A`-algebra map of the top rings, over a Noetherian `A`.
* `TauCeti.IsFractionRing.finiteDimensional_of_finite`: `Frac S` is finite-dimensional over any
  intermediate field `K`, when `S` is a finite `R`-module.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`. The statements are Stacks, Lemmas 10.36.16
and 10.36.15(2) (tags 00GQ, 00GP; "Proof. Omitted"), the Noetherian reduction sentence of
Stacks 10.161.12 (tag 032N), and the fraction-field sentence of Stacks 10.161.5 (tag 032I).
-/

public section

namespace TauCeti

/-- Source: Stacks, Lemma 10.36.16 (tag 00GQ): "Let `A → B → C` be ring maps. Let `B′` be the
integral closure of `A` in `B`, let `C′` be the integral closure of `B′` in `C`. Then `C′` is
the integral closure of `A` in `C`." Here in the form used by normalization-finiteness: if `C` is
the integral closure of `A` in `B` and `A` is integral over `R`, then `C` is the integral closure
of `R` in `B`. The converse of Mathlib's `IsIntegralClosure.tower_top`. -/
theorem IsIntegralClosure.tower_bot {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra C B] [IsScalarTower R A B]
    [IsIntegralClosure C A B] [Algebra.IsIntegral R A] : IsIntegralClosure C R B := by
  refine ⟨IsIntegralClosure.algebraMap_injective C A B, fun {x} ↦ ⟨fun hx ↦ ?_, fun hy ↦ ?_⟩⟩
  · -- integral over `R` ⇒ integral over `A`, so it is hit by `C`
    exact (IsIntegralClosure.isIntegral_iff (A := C) (R := A)).mp hx.tower_top
  · -- hit by `C` ⇒ integral over `A`, and `A` is integral over `R`
    exact isIntegral_trans x ((IsIntegralClosure.isIntegral_iff (A := C) (R := A)).mpr hy)

/-- Source: Stacks, Lemma 10.161.12 (tag 032N), proof: "Choose a finite normal field extension
`M/K` containing `L`. As `R` is Noetherian it suffices to show that the integral closure of `R`
in `M` is finite over `R`." Finiteness of integral closures descends along injective `A`-algebra
maps of the top rings. -/
theorem IsIntegralClosure.finite_of_injective {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M K' : Type*} [CommRing M] [CommRing K'] [Algebra A M] [Algebra A K'] {C C' : Type*}
    [CommRing C] [CommRing C'] [Algebra A C] [Algebra C M] [IsScalarTower A C M]
    [IsIntegralClosure C A M] [Algebra A C'] [Algebra C' K'] [IsScalarTower A C' K']
    [IsIntegralClosure C' A K'] [Module.Finite A C'] (ι : M →ₐ[A] K')
    (hι : Function.Injective ι) : Module.Finite A C := by
  -- `C → M → K'` makes `C` an algebra over which `IsIntegralClosure.lift` can land in `C'`
  let _ : Algebra C K' := (ι.toRingHom.comp (algebraMap C M)).toAlgebra
  have : IsScalarTower A C K' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply A C M a]
    exact (ι.commutes a).symm
  have : Algebra.IsIntegral A C := ⟨fun x ↦ IsIntegralClosure.isIntegral A M x⟩
  have hinj : Function.Injective (IsIntegralClosure.lift (S := C) A C' K') := fun a b hab ↦ by
    refine IsIntegralClosure.algebraMap_injective C A M (hι ?_)
    have h := congrArg (algebraMap C' K') hab
    rwa [IsIntegralClosure.algebraMap_lift, IsIntegralClosure.algebraMap_lift] at h
  exact Module.Finite.of_injective
    (IsIntegralClosure.lift (S := C) A C' K').toLinearMap hinj

/-- A fraction field `L` of a ring `S` that is finite as an `R`-module is finite-dimensional
over any intermediate field `K`, that is, any field with `R → K → L`.

This is the content of Stacks, Lemma 10.161.5 (tag 032I) — "Let `M` be a finite field extension
of the fraction field of `S`. Then `M` is also a finite field extension of `K`" — but the
hypotheses here are weaker than that sentence suggests, and deliberately so: `K` need not be a
fraction field of `R`, and no domain or torsion-freeness assumption on `R` or `S` is used.
Mathlib covers only the concrete `FractionRing R` / `FractionRing S` case. -/
theorem IsFractionRing.finiteDimensional_of_finite (R S K L : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    [Field K] [Field L] [Algebra R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] :
    FiniteDimensional K L := by
  classical
  obtain ⟨t, ht⟩ := (Module.finite_def.mp ‹Module.Finite R S›)
  -- `V` is the `K`-span of the image of a finite `R`-generating set of `S`
  set V : Submodule K L := Submodule.span K ((algebraMap S L) '' (t : Set S)) with hV
  -- every element of `S` already lies in `V`: an `R`-scalar is a `K`-scalar along `R → K → L`
  have hS : ∀ x : S, algebraMap S L x ∈ V := by
    intro x
    have hx : x ∈ Submodule.span R (t : Set S) := ht ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => simpa [map_add] using V.add_mem hy hz
    | smul r y _ hy =>
        have : algebraMap S L (r • y)
            = algebraMap R K r • algebraMap S L y := by
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R S L,
            Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K L]
        rw [this]
        exact V.smul_mem _ hy
  -- `V` absorbs multiplication by the image of `S`
  have hmul : ∀ (x : S) (v : L), v ∈ V → algebraMap S L x * v ∈ V := by
    intro x v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨y, hy, rfl⟩ := hy
        simpa [← map_mul] using hS (x * y)
    | zero => simp
    | add y z _ _ hy hz => simpa [mul_add] using V.add_mem hy hz
    | smul k y _ hy =>
        rw [Algebra.smul_def, ← mul_assoc, mul_comm (algebraMap S L x), mul_assoc,
          ← Algebra.smul_def]
        exact V.smul_mem _ hy
  -- a `K`-polynomial in an element of the image of `S` stays in `V`
  have hpoly : ∀ (b : S) (q : Polynomial K), Polynomial.aeval (algebraMap S L b) q ∈ V := by
    intro b q
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simpa [map_add] using V.add_mem hq hr
    | monomial j k =>
        have : Polynomial.aeval (algebraMap S L b) (Polynomial.monomial j k)
            = k • algebraMap S L (b ^ j) := by
          simp [Polynomial.aeval_monomial, Algebra.smul_def, map_pow]
        rw [this]
        exact V.smul_mem _ (hS _)
  -- inverses: `b⁻¹` is a `K`-polynomial in `b` divided by a nonzero constant coefficient
  have hinv : ∀ b : S, b ∈ nonZeroDivisors S → (algebraMap S L b)⁻¹ ∈ V := by
    intro b _
    have hint : IsIntegral K (algebraMap S L b) :=
      (IsIntegral.map (IsScalarTower.toAlgHom R S L) (IsIntegral.of_finite R b)).tower_top
    -- the inverse of a nonzero integral element already lies in the algebra it generates
    obtain ⟨q, hq⟩ :=
      Algebra.adjoin_mem_exists_aeval K (algebraMap S L b) hint.inv_mem_adjoin
    rw [← hq]
    exact hpoly b q
  -- `L` is the fraction field of `S`, so `V` is everything
  have htop : V = ⊤ := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) (K := L) z
    rw [div_eq_mul_inv]
    exact hmul a _ (hinv b hb)
  exact Module.finite_def.mpr
    (htop ▸ Submodule.fg_span (Set.Finite.image _ t.finite_toSet))

end TauCeti
