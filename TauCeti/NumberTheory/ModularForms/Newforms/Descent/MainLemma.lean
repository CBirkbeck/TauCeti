/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Dichotomy
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Coefficient
public import TauCeti.NumberTheory.ModularForms.Newforms.QSupport

/-!
# The Main Lemma per character (work in progress)

Miyake's Lemma 4.6.8: a cusp form `f ∈ S_k(Γ₁(N), χ)` whose Fourier coefficients vanish at every
index coprime to `N` is a sum, over the primes `p ∣ N`, of forms in `S_k(Γ₁(N), χ)` supported on
the multiples of `p`; each such summand is old. This file assembles the descent witness
(`Newforms/Descent/Coefficient.lean`) and the factor dichotomy
(`Newforms/CoprimeFilter/Dichotomy.lean`) into the inductive step and the induction over the
primes.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N p : ℕ} [NeZero N] {k : ℤ}

/-- **The inductive step of the Main Lemma** (Miyake, Lemma 4.6.8). For `f ∈ S_k(Γ₁(N), χ)` with
`χ` pulled back from `χ₀` modulo `N / p`, vanishing at every index coprime to `p L` for a
squarefree `L` coprime to `p` whose primes divide `N`, there is `f_p ∈ S_k(Γ₁(N), χ)` supported
on the multiples of `p` with `f − f_p` vanishing at every index coprime to `L`: the level-raise
`V_p` of the descent witness of level `N / p`. -/
theorem exists_mem_qSupportedOnDvdSubmodule_and_qExpansion_coeff_sub_eq_zero (hp : p.Prime)
    (hpN : p ∣ N) {L : ℕ} (hL : Squarefree L) (hLN : L.primeFactors ⊆ N.primeFactors)
    (hpL : Nat.Coprime p L) {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ∃ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k, g ∈ qSupportedOnDvdSubmodule N k p ∧
      g ∈ cuspFormCharSpace k χ ∧
      ∀ n, Nat.Coprime n L → (qExpansion 1 ⇑(f - g)).coeff n = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨F, hF, hFcoeff⟩ := exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_coeff_mul_of_coprime
    hp hpN hL hLN hpL hcomp hf hvan
  have hdvd : p * (N / p) ∣ N := dvd_of_eq (Nat.mul_div_cancel' hpN)
  refine ⟨CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) F, ?_, ?_,
    fun n hn ↦ ?_⟩
  · exact mem_qSupportedOnDvdSubmodule.mpr (qExpansionSupportedOnDvd_iff.mpr
      (CuspForm.isSupportedOnDvd_qExpansion_levelRaise (one_mem_strictPeriods_Gamma1_map _)
        (one_mem_strictPeriods_Gamma1_map _) _ F))
  · rw [hcomp]
    exact CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdvd χ₀ hF
  · rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _),
      map_sub, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
        (one_mem_strictPeriods_Gamma1_map _)]
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rw [ite_eq_left (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.pos,
        hFcoeff m (Nat.coprime_mul_iff_left.mp hn).2, sub_self]
    · rw [ite_eq_right hpn, sub_zero]
      exact hvan n (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hpn).symm hn)

end TauCeti
