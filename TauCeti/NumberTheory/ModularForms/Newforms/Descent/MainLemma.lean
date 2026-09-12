/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.AtkinLehner
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

/-! ### The induction over the primes -/

/-- The product of the primes of `S ⊆ N.primeFactors` other than `p` is squarefree, coprime to
`p`, and has its primes among those of `N`. -/
private theorem squarefree_prod_erase_and_coprime_and_primeFactors_subset {S : Finset ℕ}
    (hS : S ⊆ N.primeFactors) {p : ℕ} (hp : p.Prime) :
    Squarefree ((S.erase p).prod id) ∧ Nat.Coprime p ((S.erase p).prod id) ∧
      ((S.erase p).prod id).primeFactors ⊆ N.primeFactors := by
  have hprime : ∀ q ∈ S.erase p, q.Prime := fun q hq ↦
    Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq))
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun q₁ hq₁ q₂ hq₂ hne ↦ ?_)
      fun q hq ↦ (hprime q hq).squarefree
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hprime q₁ hq₁) (hprime q₂ hq₂)).mpr hne)
  · exact Nat.Coprime.prod_right fun q hq ↦
      (Nat.coprime_primes hp (hprime q hq)).mpr (Finset.ne_of_mem_erase hq).symm
  · exact Nat.primeFactors_mono (Finset.prod_primes_dvd N (fun q hq ↦ (hprime q hq).prime)
      fun q hq ↦ Nat.dvd_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq))) (NeZero.ne N)

omit [NeZero N] in
/-- A cusp form all of whose `q`-expansion coefficients vanish is zero. -/
private theorem eq_zero_of_forall_qExpansion_coeff_eq_zero
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (h : ∀ n, (qExpansion 1 f).coeff n = 0) :
    f = 0 := by
  have : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma1_map _)⟩
  exact DFunLike.coe_injective ((qExpansion_eq_zero_iff one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods_Gamma1_map _))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)).mp (PowerSeries.ext fun n ↦ by
      rw [map_zero]; exact h n))

/-- Splitting a sum over `S` at `p ∈ S`, when the summand at `p` is given separately. -/
private theorem sum_ite_eq_add_sum_erase {M : Type*} [AddCommMonoid M] {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S) (a : M) (g : ℕ → M) :
    ∑ q ∈ S, (if q = p then a else g q) = a + ∑ q ∈ S.erase p, g q := by
  rw [← Finset.sum_erase_add _ _ hp, add_comm, ite_eq_left rfl]
  congr 1
  exact Finset.sum_congr rfl fun q hq ↦ ite_eq_right (Finset.ne_of_mem_erase hq)

omit [NeZero N] in
/-- Extending a decomposition over `S.erase p` by a piece at `p`. -/
private theorem exists_eq_sum_of_sub_eq_sum_erase {χ : (ZMod N)ˣ →* ℂˣ} {S : Finset ℕ} {p : ℕ}
    (hpS : p ∈ S) {f gp : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hgp_supp : gp ∈ qSupportedOnDvdSubmodule N k p) (hgp_char : gp ∈ cuspFormCharSpace k χ)
    {g : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hsum : f - gp = ∑ q ∈ S.erase p, g q)
    (hsupp : ∀ q ∈ S.erase p, g q ∈ qSupportedOnDvdSubmodule N k q)
    (hchar : ∀ q ∈ S.erase p, g q ∈ cuspFormCharSpace k χ) :
    ∃ g : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k, f = ∑ p ∈ S, g p ∧
      (∀ p ∈ S, g p ∈ qSupportedOnDvdSubmodule N k p) ∧ ∀ p ∈ S, g p ∈ cuspFormCharSpace k χ := by
  refine ⟨fun q ↦ if q = p then gp else g q, ?_, fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · rw [sum_ite_eq_add_sum_erase hpS, ← hsum, add_sub_cancel]
  · by_cases hqp : q = p
    · simp only [hqp, ite_true]; exact hgp_supp
    · simp only [hqp, ite_false]
      exact hsupp q (Finset.mem_erase.mpr ⟨hqp, hq⟩)
  · by_cases hqp : q = p
    · simp only [hqp, ite_true]; exact hgp_char
    · simp only [hqp, ite_false]
      exact hchar q (Finset.mem_erase.mpr ⟨hqp, hq⟩)

/-- **The coprime sieve decomposes along the primes** (Miyake, Lemma 4.6.8, the induction). For
`S ⊆ N.primeFactors` and `f ∈ S_k(Γ₁(N), χ)` vanishing at every index coprime to the product of
`S`, `f = ∑_{p ∈ S} f_p` with each `f_p ∈ S_k(Γ₁(N), χ)` supported on the multiples of `p`. -/
theorem exists_eq_sum_of_forall_coprime_prod_qExpansion_coeff_eq_zero {χ : (ZMod N)ˣ →* ℂˣ}
    {S : Finset ℕ} (hS : S ⊆ N.primeFactors) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n (S.prod id) → (qExpansion 1 f).coeff n = 0) :
    ∃ g : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k, f = ∑ p ∈ S, g p ∧
      (∀ p ∈ S, g p ∈ qSupportedOnDvdSubmodule N k p) ∧ ∀ p ∈ S, g p ∈ cuspFormCharSpace k χ := by
  induction hcard : S.card generalizing S f with
  | zero =>
    obtain rfl : S = ∅ := Finset.card_eq_zero.mp hcard
    refine ⟨fun _ ↦ 0, ?_, fun p hp ↦ absurd hp (Finset.notMem_empty p),
      fun p hp ↦ absurd hp (Finset.notMem_empty p)⟩
    rw [Finset.sum_empty]
    exact eq_zero_of_forall_qExpansion_coeff_eq_zero fun n ↦
      hvan n (by rw [Finset.prod_empty]; exact Nat.coprime_one_right n)
  | succ m ih =>
    obtain ⟨p, hpS⟩ : S.Nonempty := Finset.card_pos.mp (hcard ▸ Nat.succ_pos m)
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (hS hpS)
    have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors (hS hpS)
    have hS' : S.erase p ⊆ N.primeFactors := fun q hq ↦ hS (Finset.mem_of_mem_erase hq)
    have hcard' : (S.erase p).card = m := by rw [Finset.card_erase_of_mem hpS, hcard]; rfl
    obtain ⟨hsq, hpL, hLN⟩ := squarefree_prod_erase_and_coprime_and_primeFactors_subset hS hp
    have hprod : S.prod id = p * (S.erase p).prod id := by
      rw [← Finset.mul_prod_erase S id hpS]; rfl
    have hvan' : ∀ n, Nat.Coprime n (p * (S.erase p).prod id) → (qExpansion 1 f).coeff n = 0 :=
      fun n hn ↦ hvan n (hprod ▸ hn)
    rcases qExpansion_coeff_eq_zero_of_coprime_or_factorsThrough χ hf hp hpN hLN hpL
      hvan' with hvan'' | hfac
    · -- `p` needs no descent: `f` already vanishes off the remaining primes
      obtain ⟨g, hsum, hsupp, hchar⟩ := ih hS' hf hvan'' hcard'
      exact exists_eq_sum_of_sub_eq_sum_erase hpS (Submodule.zero_mem _) (Submodule.zero_mem _)
        (by rw [sub_zero, hsum]) hsupp hchar
    · -- descend along `p`, then recurse on the remainder
      -- the lowered unit homomorphism, and the factorisation the descent lemmas take
      obtain ⟨χ₀, hcomp⟩ :=
        DirichletCharacter.exists_comp_unitsMap_of_factorsThrough (Nat.div_dvd_of_dvd hpN) hfac
      obtain ⟨gp, hgp_supp, hgp_char, hdiff⟩ :=
        exists_mem_qSupportedOnDvdSubmodule_and_qExpansion_coeff_sub_eq_zero hp hpN hsq hLN hpL
          hcomp hf hvan'
      obtain ⟨g, hsum, hsupp, hchar⟩ := ih hS' (Submodule.sub_mem _ hf hgp_char) hdiff hcard'
      exact exists_eq_sum_of_sub_eq_sum_erase hpS hgp_supp hgp_char hsum hsupp hchar


/-! ### The Main Lemma -/

/-- **The Main Lemma, per character** (Miyake, Lemma 4.6.8; Diamond–Shurman, Theorem 5.7.1): a
cusp form in `S_k(Γ₁(N), χ)` whose Fourier coefficients vanish at every index coprime to `N`
lies in the old subspace. It is a sum, over the primes `p ∣ N`, of forms of the same nebentypus
supported on the multiples of `p`, and each of those is old. -/
theorem mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n N → (qExpansion 1 f).coeff n = 0) : f ∈ cuspFormsOld N k := by
  obtain ⟨g, hsum, hsupp, hchar⟩ :=
    exists_eq_sum_of_forall_coprime_prod_qExpansion_coeff_eq_zero (Finset.Subset.refl _) hf
      fun n hn ↦ hvan n (Nat.coprime_of_dvd fun q hq hqn hqN ↦ hq.one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqn hn)
          (Finset.dvd_prod_of_mem id (Nat.mem_primeFactors.mpr ⟨hq, hqN, NeZero.ne N⟩))))
  have hunit : (MulChar.ofUnitHom χ).toUnitHom = χ := MulChar.equivToUnitHom.apply_symm_apply χ
  rw [hsum]
  refine Submodule.sum_mem _ fun p hp ↦
    mem_cuspFormsOld_of_qExpansionSupportedOnDvd (Nat.prime_of_mem_primeFactors hp).ne_one
      (Nat.dvd_of_mem_primeFactors hp) (MulChar.ofUnitHom χ) (by rw [hunit]; exact hchar p hp)
      (mem_qSupportedOnDvdSubmodule.mp (hsupp p hp))


end TauCeti
