/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Transfer
import TauCeti.GroupTheory.Coset.Basic

/-!
# Transitivity of the transfer homomorphism

Let `H` be a subgroup of finite index of a group `G` and let `ϕ : H →* A` be a homomorphism to a
commutative group. This file complements Mathlib's `MonoidHom.transfer` with the three structural
properties of the transfer `V_ϕ : G →* A`:

* it can be computed from any family of coset representatives indexed by a finite type, with any
  compatible labelling of the permutation action of `g`:
  `V_ϕ(g) = ∏ᵢ ϕ(t_{π i}⁻¹ g tᵢ)` whenever `g tᵢ H = t_{π i} H`;
* it is natural in the commutative target and invariant under isomorphisms of the ambient group;
* it is **transitive**: for subgroups `K ≤ H ≤ G` of finite index, the transfer from `G` to `K` is
  the transfer from `G` to `H` followed by the transfer from `H` to `K`.

## Main results

* `MonoidHom.transfer_eq_prod_of_bijective`: the transfer computed from an arbitrary indexed
  family of coset representatives.
* `MonoidHom.transfer_comp`: the transfer is natural in the commutative target.
* `MonoidHom.transfer_apply_of_mulEquiv`: the transfer is invariant under an isomorphism of
  ambient groups carrying one subgroup onto the other.
* `MonoidHom.transfer_transfer`: transitivity of the transfer along a tower `K ≤ H ≤ G`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public section

namespace MonoidHom

open Subgroup Subgroup.leftTransversals
open QuotientGroup (mk_out_smul mk_mul_out_smul)

variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A]

section

variable (ϕ : H →* A)

/-- The transfer computed from coset representatives indexed by a finite type: if `i ↦ f i H` is a
bijection onto `G ⧸ H` and `π` labels the action of `g`, in the sense that `g (f i) H = f (π i) H`,
then `transfer ϕ g = ∏ᵢ ϕ ((f (π i))⁻¹ g (f i))`. Unlike `transfer_def`, which is phrased with
a `LeftTransversal` indexed by `G ⧸ H` itself, the index type `ι` here is arbitrary; such a `π` is
automatically a permutation of `ι`. -/
theorem transfer_eq_prod_of_bijective [H.FiniteIndex] {ι : Type*} [Fintype ι] (f : ι → G)
    (hf : Function.Bijective fun i ↦ (f i : G ⧸ H)) (g : G) (π : ι → ι)
    (hπ : ∀ i, (f (π i) : G ⧸ H) = (g * f i : G)) :
    transfer ϕ g = ∏ i, ϕ ⟨(f (π i))⁻¹ * (g * f i), QuotientGroup.eq.mp (hπ i)⟩ := by
  let σ := Equiv.ofBijective _ hf
  have hσ : ∀ q, ((f (σ.symm q) : G) : G ⧸ H) = q := Equiv.ofBijective_apply_symm_apply _ hf
  let _ := H.fintypeQuotientOfFiniteIndex
  have hgσ : ∀ i, σ (π i) = g • σ i := fun i ↦ by
    simpa [σ, Equiv.ofBijective_apply, MulAction.Quotient.smul_mk] using hπ i
  rw [transfer_def ϕ ⟨_, isComplement_range_left hσ⟩, diff]
  -- Reindex the product over `G ⧸ H` along the bijection `(g • ·) ∘ σ : ι → G ⧸ H`; the factor
  -- at `g • σ i` is matched with the one at `i` using `σ⁻¹ (g • σ i) = π i`.
  refine (Fintype.prod_bijective _ ((MulAction.bijective g).comp σ.bijective) _ _ fun i ↦ ?_).symm
  simp [smul_apply_eq_smul_apply_inv_smul, IsComplement.leftQuotientEquiv_apply hσ,
    σ.symm_apply_eq.mpr (hgσ i).symm]

private theorem transfer_eq_prod_out [H.FiniteIndex] [Fintype (G ⧸ H)] (g : G) : transfer ϕ g =
    ∏ q : G ⧸ H, ϕ ⟨(g • q).out⁻¹ * (g * q.out), QuotientGroup.eq.mp (mk_out_smul g q)⟩ :=
  transfer_eq_prod_of_bijective ϕ _ (by simp) g _ (mk_out_smul g)

/-- The transfer is natural in the commutative target. -/
theorem transfer_comp [H.FiniteIndex] {B : Type*} [CommGroup B] (χ : A →* B) :
    transfer (χ.comp ϕ) = χ.comp (transfer ϕ) := by
  -- Compute both sides with the same transversal; `χ` then commutes with the product.
  ext
  simp [transfer_def _ default, diff]

/-- The transfer is invariant under an isomorphism `e : G ≃* G'` carrying `H` onto `H'`: if
`ϕ' : H' →* A` corresponds to `ϕ : H →* A` along `e`, then `transfer ϕ' (e g) = transfer ϕ g`. -/
theorem transfer_apply_of_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G') {H' : Subgroup G'}
    [H.FiniteIndex] [H'.FiniteIndex] (he : ∀ g, e g ∈ H' ↔ g ∈ H) (ϕ' : H' →* A)
    (hϕ : ∀ h : H, ϕ' ⟨e h, (he h).2 h.2⟩ = ϕ h) (g : G) : transfer ϕ' (e g) = transfer ϕ g := by
  let _ := H.fintypeQuotientOfFiniteIndex
  -- `e` carries the `Quotient.out` transversal of `H` to a transversal of `H'`, though not to
  -- the one `Quotient.out` picks there.
  rw [transfer_eq_prod_of_bijective ϕ' _ (bijective_mk_mulEquiv_out e he) (e g) (g • ·)
    (fun q ↦ by simpa [QuotientGroup.eq, ← he] using QuotientGroup.eq.mp (mk_out_smul g q)),
    transfer_eq_prod_out]
  simp [← hϕ]

end

/-- **Transitivity of the transfer.** For subgroups `K ≤ H ≤ G` of finite index, the transfer
from `G` to `K` is the transfer from `G` to `H` of the transfer from `H` to `K`; the inner
transfer is that of `ϕ` viewed on `K.subgroupOf H` via `subgroupOfEquivOfLe`. -/
theorem transfer_transfer {K : Subgroup G} (hKH : K ≤ H) [K.FiniteIndex] [H.FiniteIndex]
    (ϕ : K →* A) :
    transfer (transfer (ϕ.comp (subgroupOfEquivOfLe hKH).toMonoidHom)) = transfer ϕ := by
  let _ := H.fintypeQuotientOfFiniteIndex
  let _ := (K.subgroupOf H).fintypeQuotientOfFiniteIndex
  ext g
  -- `h q` is the element of `H` by which `g` moves the representative of `q ∈ G ⧸ H`.
  let h : G ⧸ H → H := fun q ↦
    ⟨(g • q).out⁻¹ * (g * q.out), QuotientGroup.eq.mp (mk_out_smul g q)⟩
  -- Compute the transfer to `K` with the representatives `p.out * k.out`, on which `g` acts by
  -- `(p, k) ↦ (g • p, h p • k)`.
  rw [transfer_eq_prod_out, transfer_eq_prod_of_bijective ϕ _ (bijective_mk_out_mul_out hKH) g
    (fun i ↦ (g • i.1, h i.1 • i.2)) fun _ ↦ by simp [h, mk_mul_out_smul, mul_assoc],
    Fintype.prod_prod_type]
  -- Expanding each inner transfer, the two double products agree term by term.
  simp only [transfer_eq_prod_out, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  refine Fintype.prod_congr _ _ fun p ↦ Fintype.prod_congr _ _ fun k ↦ congrArg ϕ (Subtype.ext ?_)
  -- `subgroupOfEquivOfLe_apply_coe` reads off the underlying element of `G`.
  simp [h, mul_assoc]

end MonoidHom
