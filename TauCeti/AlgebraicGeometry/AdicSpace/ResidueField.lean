/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# The residue field of a point of the valuation spectrum

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §2.4.**

A point `v : Spv A` determines a valuation `v.valuation` on `A`, but not one on a field. This file
makes it one. The support of `v` is prime, so `A ⧸ supp v` is a domain; `v.valuation` kills the
support by construction, so it descends there as `quotientValuation v`; and on the quotient it has
trivial support, which is exactly the hypothesis needed to extend it along
`A ⧸ supp v → κ(v)`, where `κ(v)` is Mathlib's `Ideal.ResidueField` of the prime ideal `supp v`.
The result, `residueFieldValuation v`, is a valuation on that **residue field**, valued in the same
`ValuativeRel.ValueGroupWithZero` as `v.valuation`.

Note that `v` itself is not a function: `Spv A` is a structure, and each of the three valuations
here has to be named. This is the factorisation the structure presheaf is read through — a section
is evaluated at `v` by its image in the residue field, and the condition cutting out `𝒪_X⁺` is
`residueFieldValuation v` of that image being `≤ 1`.

`residueFieldValuation v` also topologises `κ(v)`, through Mathlib's type synonym
`WithVal`, and the last two results describe the canonical map `A → κ(v)` for that topology: its
valuation, and its continuity when `A` is a topological ring and `v` a continuous point.

## Main definitions

* `TauCeti.ValuationSpectrum.residueRing`: the quotient `A ⧸ supp v`, a domain.
* `TauCeti.ValuationSpectrum.quotientValuation`: the valuation of `v` pushed to `A ⧸ supp v`.
* `TauCeti.ValuationSpectrum.residueFieldValuation`: the extension of the quotient valuation to
  `κ(v) = (supp v).ResidueField`. The residue field itself is Mathlib's, not a new type: the
  support is prime, and `Ideal.ResidueField` is the canonical `κ` of a prime ideal, with the
  `IsFractionRing (A ⧸ supp v) (supp v).ResidueField` instance this extension needs.

## Main results

* `TauCeti.ValuationSpectrum.quotientValuation_ne_zero`: on the residue ring the valuation has
  trivial support. Passing to the quotient is what arranges this, and it is what
  `Valuation.extendToLocalization` requires.
* `TauCeti.ValuationSpectrum.quotientValuation_comap_quotientMk` and
  `TauCeti.ValuationSpectrum.residueFieldValuation_algebraMap`: the two characteristic equations,
  saying each valuation restricts to the previous one along the canonical map.
* `TauCeti.ValuationSpectrum.residueFieldValuation_mk'`: the value of a fraction,
  `residueFieldValuation v (IsLocalization.mk' _ x s) = quotientValuation v x /
  quotientValuation v s`. With the previous lemma this computes the residue-field valuation on
  every element,
  since every element of a fraction field is a fraction, and neither needs the
  definition unfolded.
* `TauCeti.ValuationSpectrum.valued_algebraMap_residueFieldValuation`: the valuation
  topologising `κ(v)` takes the image of `a : A` to `v.valuation a`.
* `TauCeti.ValuationSpectrum.continuous_algebraMap_residueFieldValuation`: for a continuous
  point of a topological ring, `A → κ(v)` is continuous.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §2.4.

## Provenance

Adapted from `github.com/CBirkbeck/AINTLIB` @ `37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`,
Apache-2.0, file `projects/AdicSpaces/Adic spaces/CompletedResidueField.lean`: the declarations
`residueRing`, `quotientValuation`, `quotientValuation_ne_zero` and `residueFieldValuation`,
restated against TauCeti's own `Spv` API.
-/

public section

namespace TauCeti

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- The **residue ring** `A ⧸ supp v` of a point of the valuation spectrum. -/
abbrev residueRing (v : Spv A) := A ⧸ v.supp

/-- The valuation induced on the residue ring `A ⧸ supp v`. The canonical valuation of `v` has
`supp v` in its kernel — that is `TauCeti.ValuationSpectrum.supp_eq_valuation_supp` — so it
descends to the quotient. -/
noncomputable def quotientValuation (v : Spv A) :
    Valuation (residueRing v) (@ValuativeRel.ValueGroupWithZero A _ v.toValuativeRel) :=
  v.valuation.onQuot (le_of_eq v.supp_eq_valuation_supp)

/-- **On the residue ring the valuation has trivial support**: a nonzero class has nonzero
valuation. This is what passing to `A ⧸ supp v` buys, and it is the hypothesis
`Valuation.extendToLocalization` needs in order to reach the fraction field. -/
theorem quotientValuation_ne_zero (v : Spv A) {s : residueRing v} (hs : s ≠ 0) :
    quotientValuation v s ≠ 0 := by
  have hsupp : (quotientValuation v).supp = ⊥ := by
    rw [quotientValuation, Valuation.supp_quot, ← v.supp_eq_valuation_supp,
      Ideal.map_quotient_self]
  simpa only [Ne, ← Valuation.mem_supp_iff, hsupp, Ideal.mem_bot] using hs

/-- The **residue-field valuation** of a point: the quotient valuation extended along
`A ⧸ supp v → κ(v)`. Its value group is `ValuativeRel.ValueGroupWithZero`, the one `v.valuation`
already takes values in. -/
noncomputable def residueFieldValuation (v : Spv A) :
    Valuation (v.supp.ResidueField) (@ValuativeRel.ValueGroupWithZero A _ v.toValuativeRel) :=
  (quotientValuation v).extendToLocalization
    (fun _ hs ↦ quotientValuation_ne_zero v (nonZeroDivisors.ne_zero hs)) (v.supp.ResidueField)

/-- **The residue-ring valuation restricts to the valuation of `v`** along `A → A ⧸ supp v`: the
descent changes nothing on elements of `A`. This is the characteristic property of
`TauCeti.ValuationSpectrum.quotientValuation`, and the way to compute with it without unfolding
`Valuation.onQuot`. -/
@[simp]
theorem quotientValuation_comap_quotientMk (v : Spv A) :
    (quotientValuation v).comap (Ideal.Quotient.mk v.supp) = v.valuation := by
  simpa only [quotientValuation] using
    v.valuation.onQuot_comap_eq (le_of_eq v.supp_eq_valuation_supp)

/-- **The residue-field valuation restricts to the residue-ring valuation** along
`A ⧸ supp v → Frac (A ⧸ supp v)`. This is the characteristic property of
`TauCeti.ValuationSpectrum.residueFieldValuation`. -/
@[simp]
theorem residueFieldValuation_algebraMap (v : Spv A) (x : residueRing v) :
    residueFieldValuation v (algebraMap (residueRing v) (v.supp.ResidueField) x)
      = quotientValuation v x := by
  simpa only [residueFieldValuation] using
    Valuation.extendToLocalization_apply_map_apply (quotientValuation v)
      (fun _ hs ↦ quotientValuation_ne_zero v (nonZeroDivisors.ne_zero hs))
      (v.supp.ResidueField) x

/-- **The residue-field valuation on a fraction**:
`residueFieldValuation v (IsLocalization.mk' _ x s)` is
`quotientValuation v x / quotientValuation v s`. The two sides live at different stages — the
argument is a fraction of the residue field, the values are of the quotient-ring valuation.

With `TauCeti.ValuationSpectrum.residueFieldValuation_algebraMap` this computes the valuation of
every element of `κ(v)`, since every element of a fraction field is such a fraction. -/
theorem residueFieldValuation_mk' (v : Spv A) (x : residueRing v)
    (s : (nonZeroDivisors (residueRing v))) :
    residueFieldValuation v (IsLocalization.mk' (v.supp.ResidueField) x s)
      = quotientValuation v x / quotientValuation v s := by
  rw [div_eq_mul_inv]
  simpa only [residueFieldValuation] using
    Valuation.extendToLocalization_mk' (quotientValuation v)
      (fun _ hs ↦ quotientValuation_ne_zero v (nonZeroDivisors.ne_zero hs))
      (v.supp.ResidueField) x s

/-- **The valuation topologising `κ(v)` takes the image of `a : A` to `v.valuation a`.** The
residue field carries the topology of `residueFieldValuation v` through Mathlib's type synonym
`WithVal`, and `Valued.v` is that valuation.

This is the characteristic equation of `residueFieldValuation` at the level of `A` itself,
rather than of the residue ring `A ⧸ supp v`. -/
@[simp]
theorem valued_algebraMap_residueFieldValuation (v : Spv A) (a : A) :
    Valued.v (algebraMap A (WithVal (residueFieldValuation v)) a) = v.valuation a := by
  rw [WithVal.algebraMap_right_apply, WithVal.valued_toVal]
  exact (residueFieldValuation_algebraMap v (Ideal.Quotient.mk _ a)).trans <|
    DFunLike.congr_fun (quotientValuation_comap_quotientMk v) a

-- Every value of `residueFieldValuation v` is a ratio `v a / v b` of values of `v` with
-- `v b ≠ 0`. Kept private: it is the fraction bookkeeping behind the continuity proof below,
-- not API. An element of `κ(v)` is a fraction over the residue ring, and
-- `valued_algebraMap_residueFieldValuation` reads off the value of each lift to `A`.
private theorem exists_valuation_div_eq_residueFieldValuation (v : Spv A)
    (t : v.supp.ResidueField) : ∃ a b : A,
    v.valuation b ≠ 0 ∧ v.valuation a / v.valuation b = residueFieldValuation v t := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (residueRing v) t
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  -- `Valued.v` of `WithVal (residueFieldValuation v)` is `residueFieldValuation v` itself, so the
  -- characteristic equation applies to the two lifts
  have hval (c : A) : residueFieldValuation v
      (algebraMap (residueRing v) v.supp.ResidueField (Ideal.Quotient.mk v.supp c)) =
      v.valuation c := valued_algebraMap_residueFieldValuation v c
  refine ⟨a, b, ?_, ?_⟩
  · rw [← hval b, residueFieldValuation_algebraMap]
    exact quotientValuation_ne_zero v (nonZeroDivisors.ne_zero hy)
  · rw [map_div₀, hval, hval]

/-- **A continuous point maps continuously to its residue field.** If `v : Spv A` is continuous
then the canonical map `A → WithVal (residueFieldValuation v)` is continuous, `κ(v)` carrying
the topology of `residueFieldValuation v`.

Continuity is what lets the map be extended along a completion of `A`. -/
theorem continuous_algebraMap_residueFieldValuation [TopologicalSpace A] [IsTopologicalRing A]
    {v : Spv A} (hv : v.IsContinuous) :
    Continuous (algebraMap A (WithVal (residueFieldValuation v))) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  -- the radius `γ` is a ratio of two values of `residueFieldValuation v`, hence the value of a
  -- single element of `κ(v)`, which is in turn a ratio `v a / v b` of values of `v`
  obtain ⟨r, s, -, -, hrs⟩ := Valued.v.exists_div_eq_of_unit γ
  obtain ⟨a, b, hb, hab⟩ :=
    exists_valuation_div_eq_residueFieldValuation v (WithVal.ofVal (r / s))
  have hemb : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = v.valuation a / v.valuation b :=
    calc MonoidWithZeroHom.ValueGroup₀.embedding γ.1
        = Valued.v r / Valued.v s := by
          rw [← hrs, map_div₀, Valuation.embedding_restrict, Valuation.embedding_restrict]
      _ = Valued.v (r / s) := by rw [map_div₀]
      _ = residueFieldValuation v (WithVal.ofVal (r / s)) :=
          (WithVal.apply_ofVal _ (r / s)).symm
      _ = v.valuation a / v.valuation b := hab.symm
  filter_upwards [(((isContinuous_def v).mp hv).isOpen_lt_div a hb).mem_nhds
    (by simp [← hemb, zero_lt_iff])] with z hz
  rwa [Valuation.restrict_lt_iff_lt_embedding, valued_algebraMap_residueFieldValuation, hemb]

end ValuationSpectrum

end TauCeti
