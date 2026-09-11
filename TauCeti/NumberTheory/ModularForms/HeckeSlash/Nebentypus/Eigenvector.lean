/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence

/-!
# Fourier coefficients of a Hecke-ring eigenvector at the good primes

Let `F ∈ S_k(N, χ)` be an eigenvector of the `Γ₀(N)` Hecke-ring generator at a prime `p ∤ N`,
acting through `heckeRingHomCuspCharSpace`, with eigenvalue `c`. Through the identification of
that generator with the classical `T_p`
(`coe_twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0_of_prime`) and the coefficient formula
`a_m(T_p F) = a_{pm}(F) + χ(p) p^{k−1} a_{m/p}(F)` of `HeckeSlash/Recurrence.lean`, the
eigenvector equation becomes a recurrence on the Fourier coefficients of `F` alone:

`a_{pm}(F) = c · a_m(F) − χ(p) p^{k−1} a_{m/p}(F)`, the last term present only when `p ∣ m`.

Running it along the least prime factor shows that a form which is an eigenvector at *every*
good prime and has `a₁ = 0` has `a_n = 0` at every index `n` coprime to the level. This is the
form in which strong multiplicity one consumes eigen-ness: the difference of two newforms with
the same good eigenvalues has `a₁ = 1 − 1 = 0`, so all its good coefficients vanish, and the
descent argument then places it in the old subspace.

## Main results

* `HeckeRing.GL2.coe_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_prime`: the ring element
  at a prime acts on `S_k(N, χ)` as the classical `T_p`, at the level of functions.
* `HeckeRing.GL2.qExpansion_coeff_mul_of_heckeRingHomCuspCharSpace_eq_smul`: the coefficient
  recurrence of an eigenvector.
* `HeckeRing.GL2.qExpansion_coeff_eq_zero_of_coprime_of_forall_prime`: an eigenvector at every
  good prime with `a₁ = 0` has `a_n = 0` at every `n` coprime to `N`.

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

/-- **The ring element at a prime is the classical `T_p`**, on the functions underlying
the character space: `heckeTCompositeGamma0 N p` is the generator `heckeTGeneratorGamma0 N p`,
which acts through `heckeRingHomCuspCharSpace` as `heckeTCuspNat k p` does on the underlying
cusp form (`coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0`). -/
theorem coe_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_prime (hp : p.Prime)
    (F : cuspFormCharSpace k χ) :
    ⇑((heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      ⇑(heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  rw [heckeTCompositeGamma0_prime N hp,
    coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp F]

/-- **The coefficient recurrence of an eigenvector at a good prime.** If the ring generator at
`p ∤ N` acts on `F ∈ S_k(N, χ)` by the scalar `c`, then
`a_{pm}(F) = c · a_m(F) − χ(p) p^{k−1} a_{m/p}(F)`, the last term present only when `p ∣ m`. -/
theorem qExpansion_coeff_mul_of_heckeRingHomCuspCharSpace_eq_smul (hp : p.Prime)
    (hpN : Nat.Coprime p N) {F : cuspFormCharSpace k χ} {c : ℂ}
    (hF : heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) F = c • F) (m : ℕ) :
    (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p * m) =
      c * (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m -
        if p ∣ m then (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m / p) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h := qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_mem_cuspFormCharSpace
    k hp hpN χ F.2 m
  rw [← heckeTCuspNat_def, ← coe_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_prime hp F,
    hF, Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _), map_smul,
    smul_eq_mul] at h
  linear_combination -h

/-- **Coefficient vanishing from the prime eigenvalues.** A form `F ∈ S_k(N, χ)` that is an
eigenvector of the ring generator at every prime `p ∤ N` and has `a₁(F) = 0` has `a_n(F) = 0` at
every `n` coprime to `N`: the recurrence
`qExpansion_coeff_mul_of_heckeRingHomCuspCharSpace_eq_smul` along the least prime factor of `n`
expresses `a_n` through coefficients at smaller indices coprime to `N`. -/
theorem qExpansion_coeff_eq_zero_of_coprime_of_forall_prime {F : cuspFormCharSpace k χ}
    (a : ℕ → ℂ) (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p N →
      heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) F = a p • F)
    (h1 : (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 = 0) (n : ℕ)
    (hn : Nat.Coprime n N) :
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
  have hpN : Nat.Coprime n.minFac N := Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd n) hn
  have hmN : Nat.Coprime m N := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hm.symm) hn
  have hmn : m < n := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · calc m < n.minFac * m := (Nat.lt_mul_iff_one_lt_left h0).mpr hp.one_lt
        _ = n := hm.symm
  rw [hm, qExpansion_coeff_mul_of_heckeRingHomCuspCharSpace_eq_smul hp hpN (ha _ hp hpN) m,
    ih m hmn hmN, mul_zero, zero_sub]
  split_ifs with hpm
  · rw [ih (m / n.minFac) ((Nat.div_le_self m _).trans_lt hmn)
      (Nat.Coprime.coprime_div_left hmN hpm), mul_zero, neg_zero]
  · exact neg_zero

end HeckeRing.GL2
