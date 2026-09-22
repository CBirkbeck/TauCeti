/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
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

Two objects are provided, and the distinction is faithfulness.
`permutationRepresentation` is the underlying action homomorphism and needs no hypothesis; it is
injective exactly when the action on embeddings is faithful, and `permutationEquivRange` is then
the isomorphism of `Gal(M/F)` with its image in `S_n`, so the group structure is retained.

Faithfulness is the hypothesis the injectivity argument actually uses, so it is what these
declarations assume. The generation hypothesis is the usual way to meet it:
`TauCeti.FieldTheory.faithfulSMul_of_normalClosure_eq_top` turns
`normalClosure F L M = ⊤` into the instance.

## Main results

* `Equiv.permutationRepresentation`: the representation `(M ≃ₐ[F] M) →* Equiv.Perm
  (Fin n)` attached to an enumeration `e` of the embeddings.
* `Equiv.permutationRepresentation_apply`: it acts by `i ↦ e (σ • e.symm i)`.
* `Equiv.permutationRepresentation_injective`: it is injective when the action on
  embeddings is faithful.
* `Equiv.permutationEquivRange`: the resulting isomorphism of `M ≃ₐ[F] M` with the
  range of the representation, a subgroup of `Equiv.Perm (Fin n)`, with
  `Equiv.permutationEquivRange_apply` identifying its values.
* `Equiv.permutationRepresentation_eq_conj`: replacing the enumeration conjugates
  the representation, and `Equiv.permutationRepresentation_range_map_conj` says the same of the
  represented subgroups of `Equiv.Perm (Fin n)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2.
-/

public section

namespace Equiv

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
    permutationRepresentation e σ i = e (σ • e.symm i) := by
  simp only [permutationRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, MulAction.toPermHom_apply,
    MulAction.toPerm_apply]

/-- **`Gal(M/F)` embeds in `S_n`** when the action on embeddings is faithful: an automorphism
acting trivially on the enumerated embeddings fixes every embedding, hence is the identity. -/
theorem permutationRepresentation_injective [FaithfulSMul (M ≃ₐ[F] M) (L →ₐ[F] M)]
    (e : (L →ₐ[F] M) ≃ Fin n) :
    Function.Injective (permutationRepresentation (F := F) (L := L) (M := M) e) :=
  (e.permCongrHom.toEquiv.comp_injective _).2 MulAction.toPerm_injective

/-- **`Gal(M/F)` is isomorphic to a subgroup of `S_n`**, for an enumeration `e` of the embeddings
and a faithful action on them: the representation is injective, so it is an isomorphism onto its
range. -/
noncomputable def permutationEquivRange [FaithfulSMul (M ≃ₐ[F] M) (L →ₐ[F] M)]
    (e : (L →ₐ[F] M) ≃ Fin n) :
    (M ≃ₐ[F] M) ≃* (permutationRepresentation (F := F) (L := L) (M := M) e).range :=
  MonoidHom.ofInjective (permutationRepresentation_injective e)

/-- **The isomorphism acts as the representation.** -/
@[simp]
theorem permutationEquivRange_apply [FaithfulSMul (M ≃ₐ[F] M) (L →ₐ[F] M)]
    (e : (L →ₐ[F] M) ≃ Fin n) (σ : M ≃ₐ[F] M) :
    (permutationEquivRange e σ : Equiv.Perm (Fin n)) = permutationRepresentation e σ :=
  MonoidHom.ofInjective_apply _

/-- **Replacing the enumeration conjugates the representation inside `S_n`**, by the re-indexing
permutation `e.symm.trans e'`. The subgroup of `Equiv.Perm (Fin n)` is therefore well defined
only up to conjugacy, while the action on `L →ₐ[F] M` itself is canonical. -/
theorem permutationRepresentation_eq_conj (e e' : (L →ₐ[F] M) ≃ Fin n) (σ : M ≃ₐ[F] M) :
    permutationRepresentation e' σ =
      (e.symm.trans e') * permutationRepresentation e σ * (e.symm.trans e')⁻¹ := by
  ext i
  simp [Equiv.Perm.mul_apply]

/-- **The represented subgroups of `S_n` are conjugate**, by the same re-indexing permutation.
This is the subgroup-level form of `permutationRepresentation_eq_conj`, and it is what makes
"canonical up to conjugacy" a statement about the image rather than about individual elements. -/
theorem permutationRepresentation_range_map_conj (e e' : (L →ₐ[F] M) ≃ Fin n) :
    Subgroup.map (MulAut.conj (e.symm.trans e' : Equiv.Perm (Fin n))).toMonoidHom
        (permutationRepresentation (F := F) (L := L) (M := M) e).range =
      (permutationRepresentation (F := F) (L := L) (M := M) e').range := by
  ext p
  constructor
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, by simpa [MulAut.conj_apply] using permutationRepresentation_eq_conj e e' σ⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨permutationRepresentation e σ, ⟨σ, rfl⟩, by
      simpa [MulAut.conj_apply] using (permutationRepresentation_eq_conj e e' σ).symm⟩

end Equiv

end
