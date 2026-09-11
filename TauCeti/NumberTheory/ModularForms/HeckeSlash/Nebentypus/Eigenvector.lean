/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence

/-!
# Fourier coefficients of a Hecke-ring eigenvector at the good primes

Let `F ∈ M_k(N, χ)` (or `S_k(N, χ)`) be an eigenvector of the `Γ₀(N)` Hecke-ring generator at a
prime `p ∤ N`, acting through `heckeRingHomCharSpace` (`heckeRingHomCuspCharSpace`), with
eigenvalue `c`. Through the identification of that generator with the classical `T_p`
(`heckeRingHomCharSpace_heckeTGeneratorGamma0`, `heckeRingHomCuspCharSpace_heckeTGeneratorGamma0`)
and the coefficient formula `a_m(T_p F) = a_{pm}(F) + χ(p) p^{k−1} a_{m/p}(F)` of
`HeckeSlash/Recurrence.lean`, the eigenvector equation becomes a recurrence on the Fourier
coefficients of `F` alone:

`a_{pm}(F) = c · a_m(F) − χ(p) p^{k−1} a_{m/p}(F)`, the last term present only when `p ∣ m`.

Running it along the least prime factor shows that a cusp form which is an eigenvector at every
prime outside an auxiliary level `L` (a multiple of `N`) and has `a₁ = 0` has `a_n = 0` at every
index `n` coprime to `L`. This is the form in which strong multiplicity one consumes eigen-ness
(Miyake's Theorem 4.6.12 assumes agreement at the indices prime to such an `L`): the difference
of two newforms whose eigenvalues agree outside `L` has `a₁ = 1 − 1 = 0`, so its coefficients at
the indices prime to `L` all vanish, and the descent argument then places it in the old
subspace.

## Main results

* `HeckeRing.GL2.qExpansion_coeff_mul_of_heckeRingHomCharSpace_eq_smul`,
  `HeckeRing.GL2.qExpansion_coeff_mul_of_heckeRingHomCuspCharSpace_eq_smul`: the coefficient
  recurrence of an eigenvector, on `M_k(N, χ)` and on `S_k(N, χ)`.
* `HeckeRing.GL2.qExpansion_coeff_eq_zero_of_coprime_of_forall_prime`: a cusp form that is an
  eigenvector at every prime `p ∤ L` and has `a₁ = 0` has `a_n = 0` at every `n` coprime to `L`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.3.1 and §5.8.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

omit [NeZero N] in
/-- The transport of a scalar through the `m`-th Fourier coefficient. -/
private theorem qExpansion_coeff_smul {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (c : ℂ) (f : F) (m : ℕ) :
    (qExpansion 1 (c • ⇑f)).coeff m = c * (qExpansion 1 f).coeff m := by
  rw [ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _), map_smul,
    smul_eq_mul]

/-- **The coefficient recurrence of an eigenvector at a good prime, on `M_k(N, χ)`.** If the ring
generator at `p ∤ N` acts on `F ∈ M_k(N, χ)` by the scalar `c`, then
`a_{pm}(F) = c · a_m(F) − χ(p) p^{k−1} a_{m/p}(F)`, the last term present only when `p ∣ m`. -/
theorem qExpansion_coeff_mul_of_heckeRingHomCharSpace_eq_smul (hp : p.Prime)
    (hpN : Nat.Coprime p N) {F : modFormCharSpace k χ} {c : ℂ}
    (hF : heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F) (m : ℕ) :
    (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p * m) =
      c * (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m -
        if p ∣ m then (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m / p) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hT : heckeTNat k p (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    simpa [heckeTCompositeGamma0_prime N hp, heckeRingHomCharSpace_heckeTGeneratorGamma0 k χ hp]
      using congrArg Subtype.val hF
  have h := qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace
    k hp hpN χ F.2 m
  rw [← heckeTNat_def, hT, FunLike.coe_smul, qExpansion_coeff_smul] at h
  linear_combination -h

/-- **The coefficient recurrence of an eigenvector at a good prime, on `S_k(N, χ)`.** If the ring
generator at `p ∤ N` acts on `F ∈ S_k(N, χ)` by the scalar `c`, then
`a_{pm}(F) = c · a_m(F) − χ(p) p^{k−1} a_{m/p}(F)`, the last term present only when `p ∣ m`. -/
theorem qExpansion_coeff_mul_of_heckeRingHomCuspCharSpace_eq_smul (hp : p.Prime)
    (hpN : Nat.Coprime p N) {F : cuspFormCharSpace k χ} {c : ℂ}
    (hF : heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F) (m : ℕ) :
    (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p * m) =
      c * (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m -
        if p ∣ m then (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m / p) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hT : heckeTCuspNat k p (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    simpa [heckeTCompositeGamma0_prime N hp,
      heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp] using congrArg Subtype.val hF
  have h := qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_mem_cuspFormCharSpace
    k hp hpN χ F.2 m
  rw [← heckeTCuspNat_def, hT, FunLike.coe_smul, qExpansion_coeff_smul] at h
  linear_combination -h

/-- **Coefficient vanishing from the prime eigenvalues.** Let `L` be a multiple of `N`. A cusp
form `F ∈ S_k(N, χ)` that is an eigenvector of the ring generator at every prime `p ∤ L` and has
`a₁(F) = 0` has `a_n(F) = 0` at every `n` coprime to `L`: the recurrence
`qExpansion_coeff_mul_of_heckeRingHomCuspCharSpace_eq_smul` along the least prime factor of `n`
expresses `a_n` through coefficients at smaller indices coprime to `L`. The auxiliary level `L`
is the finite slack of strong multiplicity one: eigen-ness is assumed only away from finitely
many primes beyond those dividing `N`. -/
theorem qExpansion_coeff_eq_zero_of_coprime_of_forall_prime {F : cuspFormCharSpace k χ} {L : ℕ}
    (hNL : N ∣ L) (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p L →
      ∃ c : ℂ, heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F)
    (h1 : (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 = 0) (n : ℕ)
    (hn : Nat.Coprime n L) :
    (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · exact CuspFormClass.qExpansion_coeff_zero _ one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    · exact h1
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd n
  have hpL : Nat.Coprime n.minFac L := Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd n) hn
  have hmL : Nat.Coprime m L := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hm.symm) hn
  have hmn : m < n := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · calc m < n.minFac * m := (Nat.lt_mul_iff_one_lt_left h0).mpr hp.one_lt
        _ = n := hm.symm
  obtain ⟨c, hc⟩ := ha _ hp hpL
  rw [hm, qExpansion_coeff_mul_of_heckeRingHomCuspCharSpace_eq_smul hp
    (hpL.coprime_dvd_right hNL) hc m, ih m hmn hmL, mul_zero, zero_sub]
  split_ifs with hpm
  · rw [ih (m / n.minFac) ((Nat.div_le_self m _).trans_lt hmn)
      (Nat.Coprime.coprime_div_left hmL hpm), mul_zero, neg_zero]
  · exact neg_zero

end HeckeRing.GL2
