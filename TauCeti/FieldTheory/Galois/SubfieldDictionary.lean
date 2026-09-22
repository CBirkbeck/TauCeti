/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.FieldTheory.IntermediateField.Lift

-- Roadmap source: `TauCetiRoadmap/NumberFieldArithmetic/README.md` @ `2172af4ad0d3`, Layer 7.1,
-- the subfield dictionary: "Package the order-reversing equivalence between
-- `IntermediateField ℚ K` and the interval of subgroups of `Gal(M/ℚ)` containing
-- `fixingSubgroup`." The credit sits outside the module docstring deliberately: the docstring
-- documents the mathematics.

/-!
# The subfield dictionary for a field that need not be Galois

Mathlib's fundamental theorem of Galois theory, `IsGalois.intermediateFieldEquivSubgroup`,
describes the intermediate fields of a **Galois** extension `L / F` as the subgroups of
`Gal(L/F)`. It says nothing directly about the subfields of an intermediate field `K` that is
not itself Galois over `F` — and for a general number field `K` that is exactly the case of
interest, `K` being presented inside its normal closure.

The correct statement is a relative one. The subfields of `K` are an *interval*: they are the
intermediate fields of `L / F` below `K`, and under the Galois correspondence those are the
subgroups of `Gal(L/F)` **containing** `K.fixingSubgroup`. So

`IntermediateField F K ≃o (Set.Ici K.fixingSubgroup)ᵒᵈ`,

order-reversing, with the bottom `F` matching the top `⊤` and the top `K` matching
`K.fixingSubgroup` itself. Nothing here needs `K / F` to be normal; only `L / F` is Galois.

The proof is a composition of two order isomorphisms, and both halves are genuinely needed:

* `IntermediateField.liftOrderIso` identifies `IntermediateField F K` with the interval
  `Set.Iic K` inside `IntermediateField F L` — this is where the abstract field `K` is replaced
  by a subfield of `L` (`TauCeti/FieldTheory/IntermediateField/Lift.lean`);
* `IsGalois.IicOrderIso` is the Galois correspondence restricted to that interval, built from
  Mathlib's two round trips `IsGalois.fixedField_fixingSubgroup` and
  `IntermediateField.fixingSubgroup_fixedField`.

## Main results

* `IsGalois.IicOrderIso`: the intermediate fields of `L / F` below `K` correspond
  order-reversingly to the subgroups containing `K.fixingSubgroup`.
* `IsGalois.subfieldEquivSubgroup`: the dictionary, `IntermediateField F K ≃o
  (Set.Ici K.fixingSubgroup)ᵒᵈ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2.
-/

public section

open IntermediateField

namespace IsGalois

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
variable (K : IntermediateField F L)

/-- **The Galois correspondence, restricted to the intermediate fields below `K`.** These are
matched with the subgroups containing `K.fixingSubgroup`, order-reversingly. -/
noncomputable def IicOrderIso : Set.Iic K ≃o (Set.Ici K.fixingSubgroup)ᵒᵈ where
  toFun E' := OrderDual.toDual ⟨E'.1.fixingSubgroup, fixingSubgroup_le (Set.mem_Iic.1 E'.2)⟩
  invFun H := ⟨fixedField (OrderDual.ofDual H).1, by
    -- A subgroup above `K.fixingSubgroup` has fixed field below `fixedField K.fixingSubgroup`.
    have h := Set.mem_Ici.1 (OrderDual.ofDual H).2
    simpa [IsGalois.fixedField_fixingSubgroup] using fixedField_le h⟩
  left_inv E' := Subtype.ext (IsGalois.fixedField_fixingSubgroup E'.1)
  right_inv H := by
    apply OrderDual.toDual.injective
    exact Subtype.ext (fixingSubgroup_fixedField _)
  map_rel_iff' := by
    refine fun {a b} => ⟨fun h => ?_, fun h => ?_⟩
    · have h' : b.1.fixingSubgroup ≤ a.1.fixingSubgroup := h
      simpa [IsGalois.fixedField_fixingSubgroup] using fixedField_le h'
    · exact fixingSubgroup_le h

/-- **The subfield dictionary.** For `L / F` finite Galois and `K` any intermediate field, the
intermediate fields of `K / F` correspond order-reversingly to the subgroups of `Gal(L/F)`
containing `K.fixingSubgroup`. `K` itself need not be normal over `F`. -/
noncomputable def subfieldEquivSubgroup :
    IntermediateField F K ≃o (Set.Ici K.fixingSubgroup)ᵒᵈ :=
  (liftOrderIso K).trans (IicOrderIso K)

end IsGalois

end
