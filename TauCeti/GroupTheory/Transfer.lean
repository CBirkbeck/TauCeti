/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Transfer

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
  have hσ : ∀ q, ((f (σ.symm q) : G) : G ⧸ H) = q := σ.apply_symm_apply
  let _ := H.fintypeQuotientOfFiniteIndex
  have hgσ : ∀ i, σ (π i) = g • σ i := hπ
  rw [transfer_def ϕ ⟨_, isComplement_range_left hσ⟩, diff]
  -- Reindex the product over `G ⧸ H` along the bijection `σ ∘ π = (g • ·) ∘ σ : ι → G ⧸ H`.
  refine (Fintype.prod_bijective (σ ∘ π) ((funext hgσ : σ ∘ π = (g • ·) ∘ σ) ▸
    (MulAction.bijective g).comp σ.bijective) _ _ fun i ↦ ?_).symm
  simp [smul_apply_eq_smul_apply_inv_smul, IsComplement.leftQuotientEquiv_apply hσ,
    inv_smul_eq_iff.mpr (hgσ _)]

private theorem mk_out_smul (g : G) (q : G ⧸ H) : ((g • q).out : G ⧸ H) = (g * q.out : G) := by
  simp [← smul_eq_mul]

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
  have hmk : ∀ a b : G, ((e a : G') : G' ⧸ H') = e b ↔ (a : G ⧸ H) = b := by
    simp [QuotientGroup.eq, ← he]
  -- `e` carries the `Quotient.out` transversal of `H` to a transversal of `H'`, though not to
  -- the one `Quotient.out` picks there.
  have hf : Function.Bijective fun q : G ⧸ H ↦ ((e q.out : G') : G' ⧸ H') :=
    ⟨fun q q' h ↦ by simpa using (hmk _ _).1 h,
      fun q' ↦ ⟨e.symm q'.out, by simpa using (hmk _ (e.symm q'.out)).2 (QuotientGroup.out_eq' _)⟩⟩
  rw [transfer_eq_prod_of_bijective ϕ' _ hf (e g) (g • ·)
    (fun q ↦ by rw [← map_mul, hmk, mk_out_smul]), transfer_eq_prod_out]
  simp [← hϕ]

end

-- Coset representatives of `H` in `G` times coset representatives of `K` in `H` are coset
-- representatives of `K` in `G`.
private theorem bijective_mk_out_mul_out {K : Subgroup G} (hKH : K ≤ H) : Function.Bijective
    fun i : (G ⧸ H) × (H ⧸ K.subgroupOf H) ↦ ((i.1.out * (i.2.out : G) : G) : G ⧸ K) := by
  convert (quotientEquivProdOfLE hKH).symm.bijective with ⟨p, k⟩
  conv_rhs => rw [quotientEquivProdOfLE_symm_apply, ← QuotientGroup.out_eq' k, Quotient.map'_mk'']

-- In `G ⧸ K`, the representative of `h • k` (for `h ∈ H`, `k ∈ H ⧸ K`) may be replaced by `h`
-- times the representative of `k`, after left multiplication by any `a`.
private theorem mk_mul_out_smul {K : Subgroup G} (a : G) (h : H) (k : H ⧸ K.subgroupOf H) :
    ((a * (h • k).out : G) : G ⧸ K) = (a * h * k.out : G) := by
  simpa [QuotientGroup.eq, mem_subgroupOf, mul_assoc] using QuotientGroup.eq.mp (mk_out_smul h k)

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
  simp [transfer_eq_prod_out, h, mul_assoc, subgroupOfEquivOfLe]

end MonoidHom
