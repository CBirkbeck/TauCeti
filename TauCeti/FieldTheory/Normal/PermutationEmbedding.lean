/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Normal.Embeddings

-- Roadmap source: `TauCetiRoadmap/NumberFieldArithmetic/README.md` @ `2172af4ad0d3`, Layer 7.1,
-- the subfield dictionary, whose last step is exactly this: "Only after choosing
-- `e : (K →ₐ[ℚ] M) ≃ Fin (Module.finrank ℚ K)` define `permutationEmbedding : Gal(M/ℚ) ↪ S_n`.
-- Prove it injective and prove that replacing `e` conjugates the representation inside `S_n`."
-- The credit sits outside the module docstring deliberately: the docstring documents the
-- mathematics.

/-!
# The permutation representation of a Galois group on embeddings

For fields `L` and `M` over a base `F`, the group `M ≃ₐ[F] M` acts on the embeddings
`L →ₐ[F] M` by postcomposition (`TauCeti/Algebra/GroupAction/AlgHom.lean`), and when the
embedded images generate `M` that action is faithful
(`TauCeti/FieldTheory/Normal/Embeddings.lean`). This file transports that action to a concrete
symmetric group.

The set `L →ₐ[F] M` is the intrinsic object: the action on it needs no choices. A symmetric
group does not appear until an enumeration `e : (L →ₐ[F] M) ≃ Fin n` is chosen, and the point of
this file is that the choice costs exactly one conjugation and no more:

* the representation `permutationEmbedding e` depends on `e`;
* but `permutationEmbedding e'` is conjugate to it inside `Equiv.Perm (Fin n)`, by the
  re-indexing permutation `e.symm.trans e'` (`permutationEmbedding_eq_conj`).

So the action on embeddings is canonical, while the resulting subgroup of a particular symmetric
group is canonical only up to conjugacy. This is the same phenomenon as Mathlib's
`Polynomial.Gal.galActionHom`, which acts on `p.rootSet E` rather than on `Fin p.natDegree` for
the same reason.

## Main results

* `TauCeti.FieldTheory.permutationEmbedding`: the representation `(M ≃ₐ[F] M) →* Equiv.Perm
  (Fin n)` attached to an enumeration `e` of the embeddings.
* `TauCeti.FieldTheory.permutationEmbedding_apply`: it acts by `i ↦ e (σ • e.symm i)`.
* `TauCeti.FieldTheory.permutationEmbedding_injective`: it is injective when the embedded images
  generate `M`, so `Gal(M/F)` really does embed in `S_n`.
* `TauCeti.FieldTheory.permutationEmbedding_eq_conj`: replacing the enumeration conjugates the
  representation.
* `TauCeti.FieldTheory.embeddingEquivFin`: for `L/F` finite separable and `M/F` normal admitting
  an embedding of `L`, an enumeration by `Fin [L : F]`, since there are exactly `[L : F]`
  embeddings.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2.
-/

public section

namespace TauCeti.FieldTheory

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]
variable {n : ℕ}

/-- **The permutation representation on embeddings, read through an enumeration `e`.** The
underlying action on `L →ₐ[F] M` is canonical; `e` only names the points.

`@[expose]`d: the body is a transparent composition, and `permutationEmbedding_apply` is an
exported theorem whose proof has to unfold it. -/
@[expose]
noncomputable def permutationEmbedding (e : (L →ₐ[F] M) ≃ Fin n) :
    (M ≃ₐ[F] M) →* Equiv.Perm (Fin n) :=
  (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom (M ≃ₐ[F] M) (L →ₐ[F] M))

@[simp]
theorem permutationEmbedding_apply (e : (L →ₐ[F] M) ≃ Fin n) (σ : M ≃ₐ[F] M) (i : Fin n) :
    permutationEmbedding e σ i = e (σ • e.symm i) :=
  rfl

/-- **`Gal(M/F)` embeds in `S_n`** when the embedded images of `L` generate `M`: an automorphism
acting trivially on the enumerated embeddings fixes every embedding, hence is the identity. -/
theorem permutationEmbedding_injective
    (hgen : IntermediateField.normalClosure F L M = ⊤) (e : (L →ₐ[F] M) ≃ Fin n) :
    Function.Injective (permutationEmbedding (F := F) (L := L) (M := M) e) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine eq_one_of_forall_smul_eq hgen fun φ => ?_
  -- Evaluate the trivial permutation at the index `e φ` naming `φ`.
  simpa using congrArg (fun p : Equiv.Perm (Fin n) => p (e φ)) hσ

/-- **Replacing the enumeration conjugates the representation inside `S_n`**, by the re-indexing
permutation `e.symm.trans e'`. The subgroup of `Equiv.Perm (Fin n)` is therefore well defined
only up to conjugacy, while the action on `L →ₐ[F] M` itself is canonical. -/
theorem permutationEmbedding_eq_conj (e e' : (L →ₐ[F] M) ≃ Fin n) (σ : M ≃ₐ[F] M) :
    permutationEmbedding e' σ =
      (e.symm.trans e') * permutationEmbedding e σ * (e.symm.trans e')⁻¹ := by
  ext i
  simp [Equiv.Perm.mul_apply]

/-- **An enumeration of the embeddings by `Fin [L : F]`.** There are exactly `[L : F]` of them
(`AlgHom.card_of_normal`), so this is the enumeration Layer 7.1 asks for; any two differ by the
conjugation of `permutationEmbedding_eq_conj`. -/
noncomputable def embeddingEquivFin [FiniteDimensional F L] [Algebra.IsSeparable F L] [Normal F M]
    [Nonempty (L →ₐ[F] M)] : (L →ₐ[F] M) ≃ Fin (Module.finrank F L) :=
  Fintype.equivFinOfCardEq AlgHom.card_of_normal

end TauCeti.FieldTheory

end
