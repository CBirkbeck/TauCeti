/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Embeddings of a number field into a normal closure

The subfield dictionary for a number field `K` is read off the finite set of embeddings
`K →ₐ[ℚ] M` into a normal closure `M`, rather than off an unnamed ambient field. This file
specifies that closure as data and gives the action of `Gal(M/ℚ)` on the embeddings.

The Galois group acts by postcomposition, `σ • φ = σ ∘ φ`. The action is on the intrinsic set
`K →ₐ[ℚ] M`, not on `Fin n`: choosing a numbering is a separate step, and it is what makes the
resulting subgroup of a symmetric group canonical only up to conjugacy.

`NormalClosureData` records a chosen embedding, assumes `M/ℚ` is Galois, and requires the images
of `K` under all embeddings to generate `M`. That last condition is exactly what makes the
permutation representation faithful: an automorphism fixing every embedding fixes each image
pointwise, hence fixes their compositum, which is all of `M`.

## Main definitions

* `TauCeti.NumberField.NormalClosureData`: data exhibiting `M` as a normal closure of `K` over
  `ℚ`.
* `TauCeti.NumberField.embeddingAction`: `Gal(M/ℚ)` acts on `K →ₐ[ℚ] M` by postcomposition.

## Main results

* `TauCeti.NumberField.embeddingAction_apply`: the action is evaluation of `σ` after `φ`.
* `TauCeti.NumberField.NormalClosureData.eq_one_of_forall_smul_eq`: an automorphism fixing every
  embedding is the identity.
* `TauCeti.NumberField.NormalClosureData.embeddingAction_injective`: the permutation
  representation is faithful.
* `TauCeti.NumberField.NormalClosureData.card_algHom`: there are exactly `[K : ℚ]` embeddings.

Pretransitivity of the action is not proved here. It follows by lifting the isomorphism between
two embeddings' images through the normal extension `M`, but `AlgEquiv.liftNormal` requires its
domain and codomain to be fields while `AlgEquiv.ofInjectiveField` produces an equivalence onto
`AlgHom.range`, a subalgebra; bridging that with `AlgHom.fieldRange_toSubalgebra` is left to a
follow-up rather than bundled into this PR.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2 and §9.
-/

public section

open scoped NumberField
open Polynomial IntermediateField

namespace TauCeti.NumberField

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]

/-- `Gal(M/ℚ)` acts on the embeddings `K →ₐ[ℚ] M` by postcomposition. -/
instance embeddingSMul : SMul (M ≃ₐ[ℚ] M) (K →ₐ[ℚ] M) :=
  ⟨fun σ φ => σ.toAlgHom.comp φ⟩

/-- **The embedding action.** Postcomposition makes the embeddings of `K` into `M` a
`Gal(M/ℚ)`-set. -/
instance embeddingAction : MulAction (M ≃ₐ[ℚ] M) (K →ₐ[ℚ] M) where
  one_smul φ := by ext x; rfl
  mul_smul σ τ φ := by ext x; rfl

@[simp]
theorem embeddingAction_apply (σ : M ≃ₐ[ℚ] M) (φ : K →ₐ[ℚ] M) (x : K) :
    (σ • φ) x = σ (φ x) :=
  (rfl)

variable (K M) in
/-- Data exhibiting `M` as a **normal closure** of `K` over `ℚ`: a chosen embedding of `K` into a
Galois extension `M/ℚ` whose embedded images generate `M`.

The generation condition is what gives the permutation representation on `K →ₐ[ℚ] M` a trivial
kernel; without it `M` could be strictly larger than the compositum of the conjugates of `K`. -/
structure NormalClosureData [IsGalois ℚ M] where
  /-- The chosen embedding of `K` into the closure. -/
  embedding : K →ₐ[ℚ] M
  /-- The images of `K` under all embeddings generate `M`. -/
  generates : IntermediateField.normalClosure ℚ K M = ⊤

namespace NormalClosureData

variable [IsGalois ℚ M]

/-- **An automorphism fixing every embedding is the identity.** The embedded images generate `M`,
and `σ` fixes each of them pointwise, so `σ` fixes all of `M`. -/
theorem eq_one_of_forall_smul_eq (d : NormalClosureData K M) {σ : M ≃ₐ[ℚ] M}
    (h : ∀ φ : K →ₐ[ℚ] M, σ • φ = φ) : σ = 1 := by
  set H := Subgroup.closure ({σ} : Set (M ≃ₐ[ℚ] M)) with hH
  have hle : ∀ f : K →ₐ[ℚ] M, f.fieldRange ≤ IntermediateField.fixedField H := by
    intro f
    rintro _ ⟨x, rfl⟩
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
    · rintro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact congrArg (fun (ρ : K →ₐ[ℚ] M) => ρ x) (h f)
    · rfl
    · intro a b _ _ ha hb; rw [AlgEquiv.mul_apply, hb, ha]
    · intro a _ ha
      conv_lhs => rw [← ha]
      simp
  have htop : (⊤ : IntermediateField ℚ M) ≤ IntermediateField.fixedField H := by
    rw [← d.generates]
    exact iSup_le hle
  ext y
  have hy : y ∈ IntermediateField.fixedField H := htop IntermediateField.mem_top
  rw [IntermediateField.mem_fixedField_iff] at hy
  exact hy σ (Subgroup.subset_closure rfl)

/-- **The permutation representation is faithful.** Distinct automorphisms of `M` permute the
embeddings of `K` differently. -/
theorem embeddingAction_injective (d : NormalClosureData K M) :
    Function.Injective fun (σ : M ≃ₐ[ℚ] M) (φ : K →ₐ[ℚ] M) => σ • φ := by
  intro σ τ hst
  have h : ∀ φ : K →ₐ[ℚ] M, (τ⁻¹ * σ) • φ = φ := by
    intro φ
    have hσφ : σ • φ = τ • φ := congrFun hst φ
    rw [mul_smul, hσφ, inv_smul_smul]
  exact (inv_mul_eq_one.mp (d.eq_one_of_forall_smul_eq h)).symm

/-- **The number of embeddings is the degree.** `K` has exactly `[K : ℚ]` embeddings into a
normal closure, because every rational minimal polynomial of an element of `K` splits there. -/
theorem card_algHom (d : NormalClosureData K M) :
    Fintype.card (K →ₐ[ℚ] M) = Module.finrank ℚ K := by
  refine AlgHom.card_of_splits ℚ K M ?_
  intro x
  -- An embedding preserves minimal polynomials, and `M/ℚ` is normal.
  have h : minpoly ℚ (d.embedding x) = minpoly ℚ x :=
    minpoly.algHom_eq d.embedding d.embedding.injective x
  rw [← h]
  exact Normal.splits inferInstance (d.embedding x)

end NormalClosureData

end TauCeti.NumberField
