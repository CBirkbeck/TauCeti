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
but records nothing about which elements it contains or how it sits in the order on
intermediate fields of `M / K`. This file adds both, together with the universal property of
the copy of a simple extension `K⟮g⟯`: it is the smallest intermediate field of `M / K`
containing the image of `g`.

## Main results

* `TauCeti.IntermediateField.mem_extendRight`: an element of `M` lies in the copy of `F`
  exactly when it is the image of an element of `F`.
* `TauCeti.IntermediateField.extendRight_adjoin_le_iff`: the copy of `K⟮g⟯` lies inside an
  intermediate field exactly when that field contains the image of `g`.
-/

public section

open IntermediateField

namespace TauCeti.IntermediateField

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

/-- An element of `M` lies in the copy of `F` exactly when it is the image there of an element
of `F`. -/
@[simp]
theorem mem_extendRight {F : IntermediateField K L} {z : M} :
    z ∈ F.extendRight M ↔ ∃ r ∈ F, IsScalarTower.toAlgHom K L M r = z := by
  simp only [IntermediateField.extendRight, Algebra.algHom]
  exact IntermediateField.mem_map _

/-- The generator: the image of `g` lies in the copy of `K⟮g⟯`. -/
theorem algebraMap_mem_extendRight_adjoin (g : L) :
    algebraMap L M g ∈ (adjoin K {g}).extendRight M :=
  mem_extendRight.mpr ⟨g, IntermediateField.mem_adjoin_simple_self _ _,
    congrFun (IsScalarTower.coe_toAlgHom' K L M) g⟩

/-- **The universal property of the copy of a simple extension**: the copy of `K⟮g⟯` inside `M`
lies in an intermediate field exactly when that field contains the image of `g`. -/
@[simp]
theorem extendRight_adjoin_le_iff {g : L} {E : IntermediateField K M} :
    (adjoin K {g}).extendRight M ≤ E ↔ algebraMap L M g ∈ E := by
  simp only [IntermediateField.extendRight, Algebra.algHom,
    IntermediateField.map_le_iff_le_comap, IntermediateField.adjoin_le_iff,
    Set.singleton_subset_iff, SetLike.mem_coe]
  -- What is left is `g ∈ E.comap (toAlgHom …) ↔ algebraMap … g ∈ E`. Mathlib has no
  -- `IntermediateField.mem_comap`, and `Subalgebra.mem_comap` does not fire through the
  -- structure-eta in `comap`, so this last step has no named lemma and stays definitional.
  exact Iff.rfl

end TauCeti.IntermediateField

end
