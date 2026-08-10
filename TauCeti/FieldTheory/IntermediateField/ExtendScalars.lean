/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Degrees above a re-based intermediate field

`IntermediateField.extendScalars` views an intermediate field `E'` of `L / F` as an intermediate
field of `L / E`, for `E ≤ E'`. It replaces the base field and leaves the carrier alone, so the
degree of `L` above it is unchanged.

## Main results

* `IntermediateField.finrank_extendScalars`: `[L : extendScalars h] = [L : E']`.

Mathlib records the carrier equality as `IntermediateField.coe_extendScalars`, but states nothing
about degrees.
-/

public section

namespace IntermediateField

/-- **Re-basing an intermediate field does not change the degree above it**: for `E ≤ E'` in
`L / F`, the degree of `L` over `E'` viewed as an intermediate field of `L / E` is the degree of
`L` over `E'`. -/
theorem finrank_extendScalars {F L : Type*} [Field F] [Field L] [Algebra F L]
    {E E' : IntermediateField F L} (h : E ≤ E') :
    Module.finrank (extendScalars h) L = Module.finrank E' L :=
  rfl

end IntermediateField

end
