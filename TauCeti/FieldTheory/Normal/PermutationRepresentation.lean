/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Normal.Embeddings

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

* the representation `permutationRepresentation e` depends on `e`;
* but `permutationRepresentation e'` is conjugate to it inside `Equiv.Perm (Fin n)`, by the
  re-indexing permutation `e.symm.trans e'` (`permutationRepresentation_eq_conj`).

So the action on embeddings is canonical, while the resulting subgroup of a particular symmetric
group is canonical only up to conjugacy. This is the same phenomenon as Mathlib's
`Polynomial.Gal.galActionHom`, which acts on `p.rootSet E` rather than on `Fin p.natDegree` for
the same reason.

The name is `permutationRepresentation`, not `permutationEmbedding`: the declaration is a monoid
homomorphism, and it is injective only under the generation hypothesis of
`permutationRepresentation_injective`.

## Main results

* `TauCeti.FieldTheory.permutationRepresentation`: the representation `(M ≃ₐ[F] M) →* Equiv.Perm
  (Fin n)` attached to an enumeration `e` of the embeddings.
* `TauCeti.FieldTheory.permutationRepresentation_apply`: it acts by `i ↦ e (σ • e.symm i)`.
* `TauCeti.FieldTheory.permutationRepresentation_injective`: it is injective when the embedded
  images generate `M`, so `Gal(M/F)` then really does embed in `S_n`.
* `TauCeti.FieldTheory.permutationRepresentation_eq_conj`: replacing the enumeration conjugates
  the representation.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2.
-/

public section

namespace TauCeti.FieldTheory

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]
variable {n : ℕ}

/-- **The permutation representation on embeddings, read through an enumeration `e`.** The
underlying action on `L →ₐ[F] M` is canonical; `e` only names the points. -/
noncomputable def permutationRepresentation (e : (L →ₐ[F] M) ≃ Fin n) :
    (M ≃ₐ[F] M) →* Equiv.Perm (Fin n) :=
  (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom (M ≃ₐ[F] M) (L →ₐ[F] M))

/-- **The transported permutation sends an index to the index of the postcomposed embedding**:
`i` names the embedding `e.symm i`, and its image names `σ • e.symm i`. -/
@[simp]
theorem permutationRepresentation_apply (e : (L →ₐ[F] M) ≃ Fin n) (σ : M ≃ₐ[F] M) (i : Fin n) :
    permutationRepresentation e σ i = e (σ • e.symm i) :=
  (rfl)

/-- **`Gal(M/F)` embeds in `S_n`** when the embedded images of `L` generate `M`: an automorphism
acting trivially on the enumerated embeddings fixes every embedding, hence is the identity. -/
theorem permutationRepresentation_injective
    (hgen : IntermediateField.normalClosure F L M = ⊤) (e : (L →ₐ[F] M) ≃ Fin n) :
    Function.Injective (permutationRepresentation (F := F) (L := L) (M := M) e) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine eq_one_of_forall_smul_eq hgen fun φ => ?_
  -- Evaluate the trivial permutation at the index `e φ` naming `φ`.
  simpa using congrArg (fun p : Equiv.Perm (Fin n) => p (e φ)) hσ

/-- **Replacing the enumeration conjugates the representation inside `S_n`**, by the re-indexing
permutation `e.symm.trans e'`. The subgroup of `Equiv.Perm (Fin n)` is therefore well defined
only up to conjugacy, while the action on `L →ₐ[F] M` itself is canonical. -/
theorem permutationRepresentation_eq_conj (e e' : (L →ₐ[F] M) ≃ Fin n) (σ : M ≃ₐ[F] M) :
    permutationRepresentation e' σ =
      (e.symm.trans e') * permutationRepresentation e σ * (e.symm.trans e')⁻¹ := by
  ext i
  simp [Equiv.Perm.mul_apply]

end TauCeti.FieldTheory

end
