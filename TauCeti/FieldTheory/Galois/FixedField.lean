/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Fixed fields and fixing subgroups

Complements to Mathlib's Galois correspondence. A count is deliberately not given here: the file
has grown, and a number in this sentence goes stale the next time it does.

For a finite Galois extension `M / K`, a subgroup `H ≤ Gal(M/K)` and an intermediate field `E`,
the fixed field of `H` and `E` generate `M` exactly when `H` meets the fixers of `E` trivially.

The correspondence between subgroups and their fixed fields also holds with no hypothesis on
`M / K` at all, provided the subgroup is finite: Artin's theorem makes `M` finite Galois over the
fixed field of a finite `H`, and the fixers of that field are then exactly `H`. This is how a
subgroup of the automorphism group of an infinite extension is recovered from the field it cuts
out; the fixing subgroup of a subfield of finite degree is finite for the same reason.

The last results specialise the correspondence to a *cyclic* subgroup: the field fixed by a finite
cyclic `H` has `M` cyclic over it, and for `H = ⟨σ⟩` the generator is named:
`AlgEquiv.fixedFieldGenerator σ` acts on `M` as `σ` does and generates. Neither `M / K` Galois nor
`M / K` finite is needed — only that `H` be finite, which is what Mathlib's
`FixedPoints.toAlgAutMulEquiv` asks for; it identifies a finite group of automorphisms with the
Galois group of its fixed points, and that fixed-point subfield is the one underlying
`IntermediateField.fixedField`.

## Main results

* `Subgroup.fixedField_sup_eq_top_iff`
* `IntermediateField.fixingSubgroup_fixedField_of_finite`
* `IntermediateField.finite_of_finiteDimensional_fixedField`
* `IntermediateField.card_fixingSubgroup_le`
* `Subgroup.isCyclic_fixedField`
* `AlgEquiv.fixedFieldGenerator`, with `AlgEquiv.zpowers_fixedFieldGenerator_eq_top`
-/

public section

open IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]

/-- **A trivial meet of subgroups is a full join of fields.** `M ^ H` and `E` generate `M` exactly
when `H ⊓ Gal(M/E)` is trivial.

This is the Galois correspondence read in both directions: `fixingSubgroup` turns a join of fields
into a meet of subgroups, and `fixedField` turns the trivial subgroup back into `⊤`.

Stated in the `Subgroup` namespace rather than `IntermediateField`, so that `H` — the first
explicit argument, and the one `fixedField` is applied to — carries the dot notation: a consumer
writes `H.fixedField_sup_eq_top_iff E`. -/
theorem fixedField_sup_eq_top_iff (H : Subgroup (M ≃ₐ[K] M)) (E : IntermediateField K M) :
    fixedField H ⊔ E = ⊤ ↔ H ⊓ E.fixingSubgroup = ⊥ := by
  constructor
  · intro h
    have := congrArg IntermediateField.fixingSubgroup h
    rwa [fixingSubgroup_sup, fixingSubgroup_fixedField, fixingSubgroup_top] at this
  · intro h
    have hbot : (fixedField H ⊔ E).fixingSubgroup = ⊥ := by
      rw [fixingSubgroup_sup, fixingSubgroup_fixedField, h]
    have := congrArg fixedField hbot
    rwa [IsGalois.fixedField_fixingSubgroup, fixedField_bot] at this

end Subgroup

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **A finite group of automorphisms is the whole fixing subgroup of its fixed field.** Every
`K`-automorphism of `M` that fixes `M ^ H` pointwise already lies in `H`.

Mathlib's `IntermediateField.fixingSubgroup_fixedField` is the same conclusion under
`[FiniteDimensional K M]`, which is the stronger hypothesis: a finite-dimensional `M / K` has a
finite automorphism group, so every subgroup of it is finite. Finiteness of `H` is what an
infinite extension `M / K` can still supply. -/
theorem fixingSubgroup_fixedField_of_finite (H : Subgroup (M ≃ₐ[K] M)) [Finite H] :
    fixingSubgroup (fixedField H) = H := by
  refine le_antisymm (fun σ hσ ↦ ?_) ((le_iff_le _ _).mp le_rfl)
  rw [mem_fixingSubgroup_iff] at hσ
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective H M
    (AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x ↦ hσ x x.2)
  have hgσ : (g : M ≃ₐ[K] M) = σ := AlgEquiv.ext fun z ↦ congrArg (fun τ ↦ τ z) hg
  exact hgσ ▸ g.2

/-- **An intermediate field of finite degree has a finite fixing subgroup**, being a copy of the
automorphism group of a finite extension. -/
instance finite_fixingSubgroup (E : IntermediateField K M) [FiniteDimensional E M] :
    Finite (fixingSubgroup E) :=
  .of_equiv _ (fixingSubgroupEquiv E).symm.toEquiv

/-- **A group of automorphisms whose fixed field has finite degree is finite.** Thus a subgroup of
`K`-automorphisms cannot be infinite when its fixed field has finite degree in `M`. -/
theorem finite_of_finiteDimensional_fixedField (H : Subgroup (M ≃ₐ[K] M))
    [FiniteDimensional (fixedField H) M] : Finite H :=
  letI := finite_fixingSubgroup (fixedField H)
  have hH : H ≤ fixingSubgroup (fixedField H) := (le_iff_le _ _).mp le_rfl
  .of_injective (Set.inclusion hH) (Set.inclusion_injective hH)

/-- **The fixing subgroup of an intermediate field of finite degree is no larger than that
degree**, the bound on the automorphisms of a finite extension. -/
theorem card_fixingSubgroup_le (E : IntermediateField K M) [FiniteDimensional E M] :
    Nat.card (fixingSubgroup E) ≤ Module.finrank E M := by
  rw [Nat.card_congr (fixingSubgroupEquiv E).toEquiv, Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le

end IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **The field fixed by a finite cyclic group of automorphisms has cyclic Galois group.**

Both `[Finite H]` and `[IsCyclic H]` are needed: cyclicity of the Galois group is inherited from
`H`, not produced by finiteness alone. What is *not* needed is any hypothesis on `M / K`, which may
be infinite and need not be Galois. -/
theorem isCyclic_fixedField (H : Subgroup (M ≃ₐ[K] M)) [Finite H] [IsCyclic H] :
    IsCyclic (M ≃ₐ[IntermediateField.fixedField H] M) :=
  isCyclic_of_surjective _ (FixedPoints.toAlgAutMulEquiv H M).surjective

end Subgroup

namespace AlgEquiv

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

-- Source. The fixed field of `⟨σ⟩` and its named generator are the constructions pinned at
-- `TauCetiRoadmap/Chebotarev/Suggested.lean` lines 283-291, as `cyclicFixedField` and
-- `fixedFieldGenerator`. The definition below keeps the second name; the first is spelled
-- `IntermediateField.fixedField (Subgroup.zpowers σ)` throughout rather than abbreviated.

/-- **The generator of `Gal(M / M ^ ⟨σ⟩)` determined by `σ`.** Mathlib's
`FixedPoints.toAlgAutMulEquiv` identifies `⟨σ⟩` with that Galois group; this is where `σ` itself
goes, and it acts on `M` exactly as `σ` does.

Named rather than inlined so that consumers have a term to talk about: a fibre count needs the
relative Frobenius exhibited as a specific power of a specific generator, and `IsCyclic` supplies
only an anonymous one. Use `fixedFieldGenerator_apply` to compute with it and
`zpowers_fixedFieldGenerator_eq_top` for the fact that it generates.

`@[expose]` only because `fixedFieldGenerator_apply` is a bare `rfl` in an exported theorem, which
requires the body to be visible; consumers should still go through that lemma rather than unfold. -/
@[expose]
noncomputable def fixedFieldGenerator (σ : M ≃ₐ[K] M) [Finite (Subgroup.zpowers σ)] :
    M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] M :=
  FixedPoints.toAlgAutMulEquiv (Subgroup.zpowers σ) M ⟨σ, Subgroup.mem_zpowers σ⟩

/-- **The generator acts as `σ`.** This is what makes `fixedFieldGenerator σ` usable: it is a
different bundling of the same underlying map, over the fixed field rather than over `K`. -/
@[simp]
theorem fixedFieldGenerator_apply (σ : M ≃ₐ[K] M) [Finite (Subgroup.zpowers σ)] (x : M) :
    fixedFieldGenerator σ x = σ x :=
  rfl

/-- **And it generates.** The automorphisms of `M` fixing `M ^ ⟨σ⟩` are exactly the powers of
`fixedFieldGenerator σ`.

Together with `Subgroup.isCyclic_fixedField` this is the cyclic picture of `M / M ^ ⟨σ⟩` with a
named generator, and neither statement asks `M / K` to be finite or Galois. -/
theorem zpowers_fixedFieldGenerator_eq_top (σ : M ≃ₐ[K] M) [Finite (Subgroup.zpowers σ)] :
    Subgroup.zpowers (fixedFieldGenerator σ) = ⊤ := by
  -- The generation fact is proved for the underlying `toAlgAutMulEquiv` term and then transported
  -- by `exact`. It cannot be proved by rewriting with `fixedFieldGenerator`: that term lives over
  -- `FixedPoints.subfield`, which is defeq to `IntermediateField.fixedField` but not syntactically
  -- equal, so `rw` produces a type-incorrect goal.
  --
  -- Within the `have`, `MonoidHom.map_zpowers` is about a `MonoidHom`, so the `MulEquiv`
  -- application is restated through `MulEquiv.coe_toMonoidHom` rather than by unfolding the
  -- coercion. The image of `⊤` is then `Subgroup.map_equiv_top`, which `simp` reaches through
  -- `MulEquiv.toMonoidHom_eq_coe`.
  have h : Subgroup.zpowers (FixedPoints.toAlgAutMulEquiv (Subgroup.zpowers σ) M
      ⟨σ, Subgroup.mem_zpowers σ⟩) = ⊤ := by
    rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_zpowers, Subgroup.zpowers_mk_self_eq_top]
    simp
  exact h

end AlgEquiv
