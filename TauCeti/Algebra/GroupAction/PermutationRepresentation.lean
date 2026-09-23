/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.AlgHom

/-!
# The permutation representation of an automorphism group on algebra maps

For algebras `L` and `M` over a base `F`, the group `M ≃ₐ[F] M` acts on the algebra maps
`L →ₐ[F] M` by postcomposition (`TauCeti/Algebra/GroupAction/AlgHom.lean`). This file transports
that action to a concrete symmetric group, once the maps are enumerated.

Only semiring structure is involved, as for the action itself: the injectivity statements take
faithfulness of the action as a hypothesis rather than deriving it, so nothing here needs fields
or normality. The motivating case is `Gal(M/F)` permuting the embeddings of a field `L`, where
`TauCeti/FieldTheory/Normal/Embeddings.lean` supplies faithfulness from the generation
hypothesis as `faithfulSMul_of_normalClosure_eq_top`.

The set `L →ₐ[F] M` is the intrinsic object: the action on it needs no choices. A symmetric
group does not appear until an enumeration `e : (L →ₐ[F] M) ≃ Fin n` is chosen, and the point of
this file is that the choice costs exactly one conjugation and no more:

* the representation `permutationRepresentation e` depends on `e`;
* but `permutationRepresentation e'` is conjugate to it inside `Equiv.Perm (Fin n)`, by the
  re-indexing permutation `e.symm.trans e'` (`permutationRepresentation_eq_conj`).

So the action on `L →ₐ[F] M` is canonical, while the resulting subgroup of a particular
symmetric group is canonical only up to conjugacy. This is the same phenomenon as Mathlib's
`Polynomial.Gal.galActionHom`, which acts on `p.rootSet E` rather than on `Fin p.natDegree` for
the same reason.

`permutationRepresentation` is the underlying action homomorphism and needs no hypothesis. When
the action is faithful it is injective, and two bundlings of that fact are provided, differing in
what they retain: `permutationEmbedding` is the injection `(M ≃ₐ[F] M) ↪ S_n` into the ambient
symmetric group, and `permutationEquivRange` is the isomorphism onto the image, which keeps the
group structure.

## Main results

* `Equiv.permutationRepresentation`: the representation `(M ≃ₐ[F] M) →* Equiv.Perm
  (Fin n)` attached to an enumeration `e` of the algebra maps.
* `Equiv.permutationRepresentation_apply`: it acts by `i ↦ e (σ • e.symm i)`.
* `Equiv.permutationRepresentation_injective`: it is injective when the action is faithful.
* `Equiv.permutationEmbedding`: the injection `(M ≃ₐ[F] M) ↪ Equiv.Perm (Fin n)`, with
  `Equiv.permutationEmbedding_apply` identifying its values.
* `Equiv.permutationEquivRange`: the resulting isomorphism of `M ≃ₐ[F] M` with the
  range of the representation, a subgroup of `Equiv.Perm (Fin n)`, with
  `Equiv.permutationEquivRange_apply` identifying its values.
* `Equiv.permutationRepresentation_eq_conj`: replacing the enumeration conjugates
  the representation, and `Equiv.permutationRepresentation_range_map_conj` says the same of the
  represented subgroups of `Equiv.Perm (Fin n)`.

-/

public section

namespace Equiv

variable {F L M : Type*} [CommSemiring F] [Semiring L] [Semiring M] [Algebra F L]
variable [Algebra F M]
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

/-- **`M ≃ₐ[F] M` embeds in `S_n`** when the action is faithful: an automorphism acting
trivially on the enumerated maps fixes every map, hence is the identity. -/
theorem permutationRepresentation_injective [FaithfulSMul (M ≃ₐ[F] M) (L →ₐ[F] M)]
    (e : (L →ₐ[F] M) ≃ Fin n) :
    Function.Injective (permutationRepresentation (F := F) (L := L) (M := M) e) :=
  (e.permCongrHom.toEquiv.comp_injective _).2 MulAction.toPerm_injective

/-- **`M ≃ₐ[F] M` injects into `S_n`**, for an enumeration `e` of the algebra maps and a
faithful action on them. This is the ambient-group form; `permutationEquivRange` is the form
that keeps the group structure. -/
noncomputable def permutationEmbedding [FaithfulSMul (M ≃ₐ[F] M) (L →ₐ[F] M)]
    (e : (L →ₐ[F] M) ≃ Fin n) : (M ≃ₐ[F] M) ↪ Equiv.Perm (Fin n) :=
  ⟨permutationRepresentation e, permutationRepresentation_injective e⟩

/-- **The embedding acts as the representation.** -/
@[simp]
theorem permutationEmbedding_apply [FaithfulSMul (M ≃ₐ[F] M) (L →ₐ[F] M)]
    (e : (L →ₐ[F] M) ≃ Fin n) (σ : M ≃ₐ[F] M) :
    permutationEmbedding e σ = permutationRepresentation e σ :=
  (rfl)

/-- **`M ≃ₐ[F] M` is isomorphic to a subgroup of `S_n`**, for an enumeration `e` of the algebra
maps and a faithful action on them: the representation is injective, so it is an isomorphism
onto its range. -/
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
  rw [MonoidHom.map_range]
  congr 1
  ext σ
  simp [MulAut.conj_apply, permutationRepresentation_eq_conj e e' σ]

end Equiv

end
