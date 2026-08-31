/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# A simple extension of the middle field is the compositum of the generator with the base

Let `K ⊆ L ⊆ M` be a tower of fields and suppose `M` is generated over `L` by a single element
`ζ`. Then, viewed inside `M`, the compositum of `K(ζ)` with the image of `L` is already all of
`M`:

`IntermediateField.adjoin K {ζ} ⊔ (IsScalarTower.toAlgHom K L M).fieldRange = ⊤`.

The point is the change of base field: `ζ` generates `M` over `L`, and this says that the
*smaller* field `K(ζ)` — generated over the bottom of the tower — still recovers `M` once the
image of `L` is put back. That is the shape every compositum argument over the base `K` needs,
because Mathlib's engines (`IntermediateField.fixingSubgroup_sup`,
`IntermediateField.normal_sup`, and the linear-disjointness API) all take two intermediate
fields of a *single* extension `M / K` and a hypothesis that their join is `⊤`.

## Main results

* `TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top`: the compositum identity above.

## Implementation notes

The hypothesis is stated as `Algebra.adjoin L {ζ} = ⊤` — generation as an `L`-*algebra* — rather
than as `IntermediateField.adjoin L {ζ} = ⊤`, because that is the form the cyclotomic API
supplies (`IsCyclotomicExtension.adjoin_primitive_root_eq_top`). Over a field the two agree, but
taking the algebra form avoids making every caller convert.

Adapted from the Birkbeck–Brasca Chebotarev density project, where this step is inlined into a
larger `adjoin_induction`; it is separated out here because it depends on nothing but the tower.
-/

public section

namespace TauCeti.IntermediateField

/-- **The compositum step.** If `M` is generated over `L` by `ζ`, then inside `M` the
compositum of `K(ζ)` with the image of `L` is all of `M`, for any base field `K` of the
tower. This is the input to Mathlib's compositum engines
(`IntermediateField.fixingSubgroup_sup`, `IntermediateField.normal_sup`). -/
theorem adjoin_sup_fieldRange_eq_top (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] {ζ : M}
    (hadj : Algebra.adjoin L ({ζ} : Set M) = ⊤) :
    IntermediateField.adjoin K {ζ} ⊔ (IsScalarTower.toAlgHom K L M).fieldRange = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  have hx : x ∈ Algebra.adjoin L ({ζ} : Set M) := hadj ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (fun y hy ↦ ?_) (fun r ↦ ?_)
    (fun a b _ _ ha hb ↦ add_mem ha hb) (fun a b _ _ ha hb ↦ mul_mem ha hb) hx
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact le_sup_left (α := IntermediateField K M)
      (IntermediateField.mem_adjoin_simple_self K y)
  · exact le_sup_right (α := IntermediateField K M) ⟨r, rfl⟩

end TauCeti.IntermediateField
