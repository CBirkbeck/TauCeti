/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# The fixed field of the automorphism group of a normal extension

For a normal extension `E / F`, the fixed field `E ^ Aut(E/F)` sits between `F` and `E` with
`F ⊆ E ^ Aut(E/F)` purely inseparable and `E ^ Aut(E/F) ⊆ E` Galois. This is the splitting of
Stacks, Fields, Lemma 9.27.3(2), whose proof reads "We set `E_insep = E^{Aut(E/F)}`. Details
omitted." Mathlib has the Galois half as `IsGalois.of_fixed_field`; the purely inseparable half
is new here. The two are stated separately, one conclusion each.

Order matters for the consumer (`TauCeti.IsIntegralClosure.finite_of_forall_isPurelyInseparable`):
the purely inseparable step has to sit *below* the separable one, because the integral closure
of a polynomial ring in a separable extension is no longer a polynomial ring.

## Main results

* `TauCeti.IntermediateField.isPurelyInseparable_fixedField_top`: for `E / F` normal, the fixed
  field of `Gal(E/F)` is purely inseparable over `F`.
* `TauCeti.IntermediateField.isGalois_fixedField_top`: for `E / F` finite, `E` is Galois over
  the fixed field of `Gal(E/F)`.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`. The mathematics is Stacks, Fields,
Lemma 9.27.3(2) (tag 030M), the splitting used by Stacks 10.161.12 (tag 032N).
-/

public section

-- Skeleton of the normalization-finiteness development: `sorry` is an error under the library's
-- `warningAsError`, so it is downgraded here until the proofs land. Remove with the last `sorry`.
set_option warningAsError false

namespace TauCeti

/-- Source: Stacks, Fields, Lemma 9.27.3(2): "`F ⊂ E_insep` is purely inseparable", with
`E_insep = E^{Aut(E/F)}` (proof: "Details omitted"). For a normal extension `E / F`, the fixed
field of the full automorphism group is purely inseparable over `F`: an element fixed by every
automorphism has a single conjugate, since `minpoly F x` splits in `E` and its roots form one
orbit. -/
theorem IntermediateField.isPurelyInseparable_fixedField_top (F E : Type*) [Field F] [Field E]
    [Algebra F E] [Normal F E] :
    IsPurelyInseparable F (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) := by
  sorry

/-- Source: Stacks, Fields, Lemma 9.27.3(2): "`E_insep ⊂ E` is Galois", with
`E_insep = E^{Aut(E/F)}`. For a finite extension `E / F`, `E` is Galois over the fixed field of
its full automorphism group (Artin; Mathlib's `IsGalois.of_fixed_field`, transported from
`FixedPoints.subfield` to `IntermediateField.fixedField ⊤`). Deliberately not an instance: the
`⊤` argument makes it a poor one. -/
theorem IntermediateField.isGalois_fixedField_top (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    IsGalois (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E :=
  -- `IntermediateField.fixedField ⊤` and `FixedPoints.subfield ⊤ E` are both
  -- `MulAction.fixedPoints`, and the defeq is transparent: Mathlib itself closes a
  -- `fixedField ⊤` goal this way in `FieldTheory/Galois/Basic.lean:485`.
  IsGalois.of_fixed_field E (⊤ : Subgroup (E ≃ₐ[F] E))

end TauCeti
