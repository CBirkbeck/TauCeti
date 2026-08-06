/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Degree
public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Degrees of the diagonal double cosets

The degree of a diagonal double coset `T(a₁, ..., aₙ)`, in the two cases the Hecke-ring
calculations need. The scalar case `deg T(c, ..., c) = 1` holds at every positive rank, because a
scalar matrix is central. The prime-power case `deg T(pⁱ, pⁱ⁺ᵏ) = pᵏ⁻¹(p + 1)` for `k ≥ 1`
is specific to rank two: the degree of a double coset is the relative index of the
conjugated copy of `SL₂(ℤ)`, which for a diagonal representative is exactly the index
`[SL₂(ℤ) : Γ₀(pᵏ)]` computed in `TauCeti.NumberTheory.ModularForms.CongruenceSubgroups`.

Both live here rather than under `GL2` because the rank-two formula is a shared prerequisite
of the planned `GL2.MultiplicationTable` and `GL2.Degree` developments alike and must sit
below both, while the scalar formula is rank-general. Those consumers are not yet in the
repository; this file is the prerequisite that unblocks them.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/Degree.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).  Note the degree of `T(a₁,...,aₙ)` is **not** `∏_{i<j}(aⱼ/aᵢ)`: for
`a = (1, p)` that count is `p`, while the true degree is `p + 1` — the double coset also
contains representatives with permuted diagonals.

## Main results

* `degree_diagCoset_prime_pow`: `deg T(pⁱ, pⁱ⁺ᵏ) = pᵏ⁻¹(p + 1)` for prime `p`, `k ≥ 1`.
* `degree_diagCoset_scalar`: `deg T(c, ..., c) = 1`, at every positive rank.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Propositions 3.14, 3.18 and Theorem 3.24.
-/

public section

open HeckeRing Finset CongruenceSubgroup Matrix.SpecialLinearGroup Matrix
open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

variable (n : ℕ) [NeZero n]

private lemma a1_eq_a0_mul_pk {p : ℕ} {a : Fin 2 → ℕ} {k : ℕ}
    (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) :
    (a 1 : ℚ) = (a 0 : ℚ) * (↑(p ^ k) : ℚ) := by
  have h1 := Nat.div_mul_cancel h_dvd_a
  rw [h_ratio] at h1
  push_cast [← h1]; ring

private lemma conj_natDiagGL_mem_of_Gamma0 (p : ℕ) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) (σ : SL(2, ℤ))
    (hσ : (↑(p ^ k) : ℤ) ∣ σ.1 1 0) :
    (natDiagGL 2 a)⁻¹ * (σ : GL (Fin 2) ℚ) * natDiagGL 2 a ∈ SLnZ 2 := by
  obtain ⟨c, hc⟩ := hσ
  let τ_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![σ.1 0 0, ↑(p ^ k) * σ.1 0 1; c, σ.1 1 1]
  have h_det : τ_mat.det = 1 := by
    simp only [τ_mat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hσ_det := σ.prop; simp only [Matrix.det_fin_two] at hσ_det
    rw [hc] at hσ_det; linarith
  let τ : SL(2, ℤ) := ⟨τ_mat, h_det⟩
  refine (mem_SLnZ_iff 2).mpr ⟨τ, ?_⟩
  have ha1 := a1_eq_a0_mul_pk h_ratio h_dvd_a
  have hcQ : (σ.1 1 0 : ℚ) = (↑(p ^ k) : ℚ) * (c : ℚ) := by exact_mod_cast hc
  push_cast at ha1 hcQ
  suffices h : natDiagGL 2 a * (τ : GL (Fin 2) ℚ) = (σ : GL (Fin 2) ℚ) * natDiagGL 2 a by
    have h' := congr_arg ((natDiagGL 2 a)⁻¹ * ·) h
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h'; exact h'
  apply Units.ext
  have hval : ∀ μ : SL(2, ℤ), (↑(mapGL ℚ μ) : Matrix _ _ ℚ) = μ.val.map (Int.cast) :=
    fun μ ↦ by simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
  simp only [Units.val_mul, hval]
  ext i j
  simp only [natDiagGL_coe 2 a ha, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [τ, τ_mat, Matrix.of_apply, Matrix.cons_val', Fin.isValue] <;>
    push_cast <;> (try rw [hcQ]) <;> (try rw [ha1]) <;> ring

private lemma Gamma0_of_conj_natDiagGL_mem (p : ℕ) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) (σ : SL(2, ℤ))
    (hmem : (natDiagGL 2 a)⁻¹ * (σ : GL (Fin 2) ℚ) * natDiagGL 2 a ∈ SLnZ 2) :
    (↑(p ^ k) : ℤ) ∣ σ.1 1 0 := by
  obtain ⟨τ, hτ⟩ := (mem_SLnZ_iff 2).mp hmem
  have ha1 := a1_eq_a0_mul_pk h_ratio h_dvd_a
  have ha0_ne : (a 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ha 0).ne'
  have h_mul : natDiagGL 2 a * (τ : GL (Fin 2) ℚ) = (σ : GL (Fin 2) ℚ) * natDiagGL 2 a := by
    have := congr_arg (natDiagGL 2 a * ·) hτ
    simp only [← mul_assoc, mul_inv_cancel, one_mul] at this; exact this
  have h_entry : (a 1 : ℚ) * (τ.1 1 0 : ℚ) = (σ.1 1 0 : ℚ) * (a 0 : ℚ) := by
    have h10 := Units.ext_iff.mp h_mul
    have := congr_arg (fun M ↦ M 1 0) h10
    simpa only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
      natDiagGL_coe 2 a ha, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.map_apply, algebraMap_int_eq, eq_intCast] using this
  have h_σ₁₀ : (σ.1 1 0 : ℚ) = ↑(p ^ k) * (τ.1 1 0 : ℚ) := by
    rw [ha1] at h_entry; field_simp at h_entry ⊢; linarith
  exact ⟨τ.1 1 0, by exact_mod_cast h_σ₁₀⟩

private lemma conjDiag_relIndex_eq_Gamma0_index (p : ℕ) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) :
    (ConjAct.toConjAct (natDiagGL 2 a) • SLnZ 2).relIndex (SLnZ 2) =
    (Gamma0 (p ^ k)).index := by
  set H := SLnZ 2
  set α := natDiagGL 2 a
  set f := (mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ)
  have h_inj : Function.Injective f := mapGL_injective
  have h_H_eq : H = Subgroup.map f ⊤ := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    exact (mem_SLnZ_iff 2).trans (by simp [f])
  have h_gamma0_iff : ∀ σ : SL(2, ℤ),
      σ ∈ Gamma0 (p ^ k) ↔ α⁻¹ * f σ * α ∈ H := by
    intro σ
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨conj_natDiagGL_mem_of_Gamma0 p a ha k h_ratio h_dvd_a σ,
           Gamma0_of_conj_natDiagGL_mem p a ha k h_ratio h_dvd_a σ⟩
  have h_inf_eq : (ConjAct.toConjAct α • H) ⊓ H = Subgroup.map f (Gamma0 (p ^ k)) := by
    ext g; simp only [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨h_smul, h_mem⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h_smul
      obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff 2).mp h_mem
      exact ⟨σ, (h_gamma0_iff σ).mpr h_smul, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨?_, coe_mem_SLnZ 2 σ⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      exact (h_gamma0_iff σ).mp hσ
  calc (ConjAct.toConjAct α • H).relIndex H
      = ((ConjAct.toConjAct α • H) ⊓ H).relIndex H :=
        (Subgroup.inf_relIndex_right _ _).symm
    _ = (Subgroup.map f (Gamma0 (p ^ k))).relIndex (Subgroup.map f ⊤) := by
        rw [h_inf_eq, h_H_eq]
    _ = (Gamma0 (p ^ k)).relIndex ⊤ :=
        Subgroup.relIndex_map_map_of_injective _ _ h_inj
    _ = (Gamma0 (p ^ k)).index := (Gamma0 (p ^ k)).relIndex_top_right

/-- **The prime-power degree** (Shimura, Theorem 3.24, degree count): for prime `p`,
`deg T(pⁱ, pⁱ⁺ᵏ) = pᵏ⁻¹ (p + 1)` for `k ≥ 1`. -/
theorem degree_diagCoset_prime_pow (p : ℕ) (hp : Nat.Prime p) (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hdiv : IsDvdChain a) (k : ℕ) (hk : 0 < k)
    (h_ratio : a 1 / a 0 = p ^ k) :
    (diagCoset a).degree = p ^ (k - 1) * (p + 1) := by
  -- `degree_mk` already computes the degree from an explicit representative, so only the
  -- relative index at `natDiagGL` is left to identify
  rw [diagCoset_def, HeckeCoset.degree_mk,
    conjDiag_relIndex_eq_Gamma0_index p a ha k h_ratio (isDvdChain_iff.mp hdiv (Fin.zero_le 1)),
    Gamma0_prime_power_index p hp k hk]

private lemma natDiagGL_comm_of_const (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (h_const : ∀ i, a i = a 0) (g : GL (Fin n) ℚ) :
    natDiagGL n a * g = g * natDiagGL n a := by
  apply Units.ext
  simp only [Units.val_mul, natDiagGL_coe n a ha]
  have h_diag : Matrix.diagonal (fun i ↦ (a i : ℚ)) =
      (a 0 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs with h
    · subst h; simp [h_const]
    · simp
  rw [h_diag, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- **The scalar degree**: a scalar diagonal matrix is central, so its double coset is a
single coset and `deg T(c, ..., c) = 1`. -/
@[simp]
theorem degree_diagCoset_scalar (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (h_const : ∀ i, a i = a 0) : (diagCoset a).degree = 1 := by
  rw [diagCoset_def, HeckeCoset.degree_mk]
  have h_diag_conj : ∀ g : GL (Fin n) ℚ,
      (natDiagGL n a)⁻¹ * g * natDiagGL n a = g := fun g ↦ by
    rw [mul_assoc, ← natDiagGL_comm_of_const n a ha h_const g, ← mul_assoc,
      inv_mul_cancel, one_mul]
  have h_smul_diag : ConjAct.toConjAct (natDiagGL n a) • SLnZ n = SLnZ n := by
    ext x
    simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      map_inv, ConjAct.ofConjAct_toConjAct, inv_inv, h_diag_conj]
  rw [h_smul_diag, Subgroup.relIndex_self]

end HeckeRing.GLn
