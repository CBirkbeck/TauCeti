/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.ExtendRight

/-!
# Membership and order for `IntermediateField.extendRight`

For a tower `K ⊆ L ⊆ M`, `IntermediateField.extendRight F M` is the copy of an intermediate
field `F` of `L / K` inside `M`. Mathlib defines it and transfers algebra structure along it,
but records nothing about how it sits in the order on intermediate fields of `M / K`. This file
adds that, together with the universal property of the copy of a simple extension `K⟮g⟯`: it is
the smallest intermediate field of `M / K` containing the image of `g`.

## Main results

* `TauCeti.IntermediateField.extendRight_le_iff`: the copy of `F` lies below an intermediate
  field exactly when that field contains every image from `F`.
* `TauCeti.IntermediateField.extendRight_adjoin_le_iff`: the copy of `K⟮g⟯` lies inside an
  intermediate field exactly when that field contains the image of `g`.
-/

public section

open IntermediateField

namespace TauCeti.IntermediateField

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

/-- **The copy of `F` is below an intermediate field exactly when that field contains every
image from `F`.** This is the order characterisation: it decides an inclusion pointwise, with no
`comap` and no unfolding of `extendRight` at the call site. -/
-- Not `@[simp]`: it and `extendRight_adjoin_le_iff` below cannot both be, since this rewrites
-- that one's left-hand side and `simpNF` rejects the pair. The simple-extension form is the
-- one worth reaching automatically, so it keeps the attribute and this is applied by name.
theorem extendRight_le_iff {F : IntermediateField K L} {E : IntermediateField K M} :
    F.extendRight M ≤ E ↔ ∀ x ∈ F, algebraMap L M x ∈ E := by
  simp only [IntermediateField.extendRight, Algebra.algHom, SetLike.le_def,
    IntermediateField.mem_map, forall_exists_index, and_imp]
  exact ⟨fun h x hx => h x hx (congrFun (IsScalarTower.coe_toAlgHom' K L M) x),
    fun h _ x hx hxz => hxz ▸ h x hx⟩

/-- The generator: the image of `g` lies in the copy of `K⟮g⟯`. -/
theorem algebraMap_mem_extendRight_adjoin (g : L) :
    algebraMap L M g ∈ (adjoin K {g}).extendRight M := by
  simp only [IntermediateField.extendRight, Algebra.algHom, IntermediateField.mem_map]
  exact ⟨g, IntermediateField.mem_adjoin_simple_self _ _,
    congrFun (IsScalarTower.coe_toAlgHom' K L M) g⟩

/-- **The universal property of the copy of a simple extension**: the copy of `K⟮g⟯` inside `M`
lies in an intermediate field exactly when that field contains the image of `g`. -/
@[simp]
theorem extendRight_adjoin_le_iff {g : L} {E : IntermediateField K M} :
    (adjoin K {g}).extendRight M ≤ E ↔ algebraMap L M g ∈ E := by
  rw [extendRight_le_iff]
  refine ⟨fun h => h g (IntermediateField.mem_adjoin_simple_self _ _), fun hg x hx => ?_⟩
  -- `K⟮g⟯` is the smallest intermediate field containing `g`, so it lies in the preimage of `E`
  -- as soon as `g` does; `x` is then carried along.
  have : adjoin K {g} ≤ E.comap (IsScalarTower.toAlgHom K L M) :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hg)
  exact this hx

end TauCeti.IntermediateField

end
