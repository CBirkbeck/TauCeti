/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Intermediate fields of an intermediate field

For `E` an intermediate field of `L / F`, the intermediate fields of `E / F` are the intermediate
fields of `L / F` lying below `E`. Mathlib supplies the two maps — `IntermediateField.lift` and
`IntermediateField.restrict` — and one of the two round trips (`lift_restrict`). This file adds
the other round trip and the order-embedding statement, and packages them as an order
isomorphism

`IntermediateField F E ≃o Set.Iic E`.

Having the correspondence as a single `OrderIso` rather than as a pair of monotone maps is what
lets it be composed with the Galois correspondence, which is also an `OrderIso`; that composition
is the subfield dictionary of
`TauCeti/FieldTheory/Galois/SubfieldDictionary.lean`.

## Main results

* `IntermediateField.restrict_lift`: restricting a lifted intermediate field recovers it. This
  is the round trip Mathlib does not state; `lift_restrict` is the other one.
* `IntermediateField.lift_le_lift_iff`: `lift` reflects as well as preserves the order.
* `IntermediateField.liftOrderIso`: the resulting order isomorphism with `Set.Iic E`, with
  `IntermediateField.liftOrderIso_apply` and `IntermediateField.liftOrderIso_symm_apply` giving
  its two directions as `lift` and `restrict`.
-/

public section

namespace IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {E : IntermediateField F L}

/-- **Restricting a lifted intermediate field recovers it.** This is the round trip complementary
to Mathlib's `lift_restrict`. -/
theorem restrict_lift (E' : IntermediateField F E) : restrict (lift_le E') = E' := by
  ext x
  rw [mem_restrict, mem_lift]

/-- **`lift` reflects the order.** Monotonicity alone would only give one direction; the converse
is what makes `liftOrderIso` an order isomorphism rather than a monotone bijection. -/
theorem lift_le_lift_iff {a b : IntermediateField F E} : lift a ≤ lift b ↔ a ≤ b := by
  constructor
  · intro h x hx
    exact (mem_lift x).1 (h ((mem_lift x).2 hx))
  · intro h y hy
    -- A member of `lift a` lies in `E`, so it has a name as an element of `E`.
    have hyE : y ∈ E := lift_le a hy
    exact (mem_lift (⟨y, hyE⟩ : E)).2 (h ((mem_lift (⟨y, hyE⟩ : E)).1 hy))

variable (E) in
/-- **The intermediate fields of `E / F` are the intermediate fields of `L / F` below `E`**, as an
order isomorphism. -/
def liftOrderIso : IntermediateField F E ≃o Set.Iic E where
  toFun E' := ⟨lift E', lift_le E'⟩
  invFun E' := restrict E'.2
  left_inv E' := restrict_lift E'
  right_inv E' := Subtype.ext (lift_restrict E'.2)
  map_rel_iff' := lift_le_lift_iff

@[simp]
theorem liftOrderIso_apply (E' : IntermediateField F E) :
    liftOrderIso E E' = ⟨lift E', lift_le E'⟩ :=
  (rfl)

@[simp]
theorem liftOrderIso_symm_apply (E' : Set.Iic E) :
    (liftOrderIso E).symm E' = restrict E'.2 :=
  (rfl)

end IntermediateField

end
