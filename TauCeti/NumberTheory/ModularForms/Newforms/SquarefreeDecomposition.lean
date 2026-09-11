/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ConductorDichotomy
public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Basic

/-!
# The squarefree decomposition of a form with vanishing coprime coefficients

Miyake's Lemma 4.6.7: a cusp form `f ∈ S_k(Γ₁(N), χ)` whose `q`-expansion vanishes at every index
coprime to a squarefree `l > 1` is, coefficient by coefficient, a sum `∑_{q ∣ l} V_q g_q` of
level-raises of forms `g_q` of level `N l²`, each `g_q` the restriction of a form `F_q` of level
`N l² / q` with a nebentypus lowered along `N l² / q ∣ N l²`.

## Main results

* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd`:
  the peeling step — a form of level `M` supported on the multiples of a prime `p ∣ M` is, on
  coefficients, the level-raise `V_p` of a form of level `M / p` with a lowered nebentypus.
* `TauCeti.exists_qExpansion_coeff_eq_sum_primeFactors_of_squarefree`: Lemma 4.6.7.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/SquarefreeDecomp.lean`,
theorem `squarefree_decomp_with_lower_level` and its `Miyake467Decomp_*` helpers. The source
states the decomposition through a bundled `Prop`-valued definition and transports forms across
equalities of levels; here the conclusion is stated directly, levels are related by divisibility
(`CuspForm.ofLe`), and the per-prime peeling is one public lemma instead of two dichotomy
branches repeated in the base case and the inductive step.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.7.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {k : ℤ}

/-- The coefficients of a level-raise, read backwards: if `G = p ^ (1 - k) • (g ∣[k] diag(p, 1))`
as functions on `ℍ`, that is `G = V_p g`, then `a_m(g) = a_{pm}(G)`. (Public in `Degeneracy.lean`
once #6319 lands; this copy goes then.) -/
private theorem qExpansion_coeff_eq_qExpansion_coeff_mul_of_coe_eq {M p : ℕ} [NeZero p]
    (hpM : p ∣ M) {G : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    {g : CuspForm ((Gamma1 (M / p)).map (mapGL ℝ)) k}
    (h : ⇑G = (p : ℂ) ^ (1 - k) • (⇑g ∣[k] scaleGL p)) (m : ℕ) :
    (qExpansion 1 g).coeff m = (qExpansion 1 G).coeff (p * m) := by
  have hG : G = CuspForm.levelRaise p
      (Gamma1_map_le_conjAct_scaleGL_of_dvd (dvd_of_eq (Nat.mul_div_cancel' hpM))) g :=
    DFunLike.coe_injective (by rw [CuspForm.coe_levelRaise, h])
  rw [hG, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
    (one_mem_strictPeriods_Gamma1_map _)]
  simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left m (NeZero.pos p)]

/-- **Peeling a prime off a form supported on its multiples.** If `G ∈ S_k(Γ₁(M), χ ∘ π)` is
supported on the multiples of a prime `p ∣ M`, where `χ` has level `N ∣ M / p`, then there is a
form `F ∈ S_k(Γ₁(M / p), χ')` with `χ'` lying over `χ ∘ π` and `a_n(G) = a_{n/p}(F)` for `p ∣ n`,
`a_n(G) = 0` otherwise: `G` is `V_p F` on coefficients. The level-lowering dichotomy provides `F`
with the lowered nebentypus, or forces `G = 0`, in which case `F = 0` does. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd
    {M N : ℕ} [NeZero M] (χ : (ZMod N)ˣ →* ℂˣ) (hNM : N ∣ M) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M)
    (hNMp : N ∣ M / p) {G : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hG : G ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)))
    (hsupp : QExpansionSupportedOnDvd p G) :
    ∃ (χ' : (ZMod (M / p))ˣ →* ℂˣ) (F : CuspForm ((Gamma1 (M / p)).map (mapGL ℝ)) k),
      F ∈ cuspFormCharSpace k χ' ∧
        χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)) = χ.comp (ZMod.unitsMap hNM) ∧
        ∀ n, (qExpansion 1 G).coeff n = if p ∣ n then (qExpansion 1 F).coeff (n / p) else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨φ, hGφ, hφT⟩ :=
    CuspForm.exists_eq_smul_slash_scaleGL_and_slash_T_eq_of_qExpansionSupportedOnDvd G hsupp
  have hGχ : G ∈
      cuspFormCharSpace k (MulChar.ofUnitHom (χ.comp (ZMod.unitsMap hNM))).toUnitHom := by
    rwa [show (MulChar.ofUnitHom (χ.comp (ZMod.unitsMap hNM))).toUnitHom =
      χ.comp (ZMod.unitsMap hNM) from MulChar.equivToUnitHom.apply_symm_apply _]
  rcases exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero hpM k _ φ G hGχ hGφ hφT with
    ⟨hfac, F, hFχ, hFφ⟩ | hφ0
  · refine ⟨hfac.χ₀.toUnitHom, F, hFχ, ?_, fun n ↦ ?_⟩
    · rw [← DirichletCharacter.changeLevel_toUnitHom, ← hfac.eq_changeLevel]
      exact MulChar.equivToUnitHom.apply_symm_apply _
    · by_cases hn : p ∣ n
      · obtain ⟨m, rfl⟩ := hn
        simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left m hp.pos]
        exact (qExpansion_coeff_eq_qExpansion_coeff_mul_of_coe_eq hpM (hFφ ▸ hGφ) m).symm
      · simp only [hn, ↓reduceIte]
        exact PowerSeries.isSupportedOnDvd_iff.mp (qExpansionSupportedOnDvd_iff.mp hsupp) n hn
  · have hG0 : (⇑G : ℍ → ℂ) = 0 := by rw [hGφ, hφ0, SlashAction.zero_slash, smul_zero]
    refine ⟨χ.comp (ZMod.unitsMap hNMp), 0, Submodule.zero_mem _, ?_, fun n ↦ ?_⟩
    · rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
    · rw [hG0, qExpansion_zero, map_zero, FunLike.coe_zero, qExpansion_zero]
      simp only [map_zero, ite_self]

variable {N : ℕ} [NeZero N]

/-- The conclusion of Lemma 4.6.7 at level `N * l ^ 2`, as a predicate on `f`: families `g`, `F`
and `χ'` indexed by the primes of `l`, with `g q` of level `N * l ^ 2` in the space of `χ`, `F q`
of level `N * l ^ 2 / q` in the space of `χ' q` lying over `χ`, `F q` and `g q` the same function,
and `a_n(f) = ∑_{q ∣ l, q ∣ n} a_{n/q}(g q)`. Only used to state the induction. -/
private def SquarefreeDecomposition (χ : (ZMod N)ˣ →* ℂˣ) (l : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∃ (g : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
    (F : ∀ q ∈ l.primeFactors, CuspForm ((Gamma1 (N * l ^ 2 / q)).map (mapGL ℝ)) k)
    (χ' : ∀ q ∈ l.primeFactors, (ZMod (N * l ^ 2 / q))ˣ →* ℂˣ),
    (∀ q ∈ l.primeFactors,
      g q ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2))))) ∧
    (∀ q (hq : q ∈ l.primeFactors), F q hq ∈ cuspFormCharSpace k (χ' q hq)) ∧
    (∀ q (hq : q ∈ l.primeFactors), ⇑(F q hq) = ⇑(g q)) ∧
    (∀ q (hq : q ∈ l.primeFactors),
      (χ' q hq).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_pow_self l two_ne_zero))
          N))) =
        χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2)))) ∧
    ∀ n, (qExpansion 1 f).coeff n =
      ∑ q ∈ l.primeFactors, if q ∣ n then (qExpansion 1 (g q)).coeff (n / q) else 0

omit [NeZero N] in
/-- Assembling the decomposition at `l = q * l'` from the data at the prime `q` and the families
over the primes of `l'`, all already read at the levels `N * l ^ 2` and `N * l ^ 2 / q'`. -/
private theorem squarefreeDecomposition_of_insert {χ : (ZMod N)ˣ →* ℂˣ} {l q l' : ℕ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hq : q.Prime) (hl : l = q * l')
    (hql' : q ∉ l'.primeFactors) (hl' : l' ≠ 0)
    (g' : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
    (F' : ∀ q' ∈ l'.primeFactors, CuspForm ((Gamma1 (N * l ^ 2 / q')).map (mapGL ℝ)) k)
    (χ'' : ∀ q' ∈ l'.primeFactors, (ZMod (N * l ^ 2 / q'))ˣ →* ℂˣ)
    (hg' : ∀ q' ∈ l'.primeFactors,
      g' q' ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2)))))
    (hF' : ∀ q' (hq' : q' ∈ l'.primeFactors), F' q' hq' ∈ cuspFormCharSpace k (χ'' q' hq'))
    (hF'g' : ∀ q' (hq' : q' ∈ l'.primeFactors), ⇑(F' q' hq') = ⇑(g' q'))
    (hχ'' : ∀ q' (hq' : q' ∈ l'.primeFactors),
      (χ'' q' hq').comp (ZMod.unitsMap (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right
        ((Nat.dvd_of_mem_primeFactors hq').trans (dvd_pow_self l' two_ne_zero) |>.trans
          (pow_dvd_pow_of_dvd (hl ▸ dvd_mul_left l' q) 2)) N))) =
        χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2))))
    (F : CuspForm ((Gamma1 (N * l ^ 2 / q)).map (mapGL ℝ)) k) (χ₁ : (ZMod (N * l ^ 2 / q))ˣ →* ℂˣ)
    (hF : F ∈ cuspFormCharSpace k χ₁)
    (hχ₁ : χ₁.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
      (dvd_mul_of_dvd_right ((hl ▸ dvd_mul_right q l').trans (dvd_pow_self l two_ne_zero)) N))) =
      χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2))))
    (hcoeff : ∀ n, (qExpansion 1 f).coeff n =
      (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0) +
        ∑ q' ∈ l'.primeFactors, if q' ∣ n then (qExpansion 1 (g' q')).coeff (n / q') else 0) :
    SquarefreeDecomposition χ l f := by
  have hql : q ∣ l := hl ▸ dvd_mul_right q l'
  have hqN : N * l ^ 2 / q ∣ N * l ^ 2 :=
    Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right (hql.trans (dvd_pow_self l two_ne_zero)) N)
  have hpf : l.primeFactors = insert q l'.primeFactors := by
    rw [hl, Nat.primeFactors_mul hq.ne_zero hl', hq.primeFactors, Finset.singleton_union]
  have hmem : ∀ {q'}, q' ∈ l.primeFactors → q' ≠ q → q' ∈ l'.primeFactors := fun h hne ↦ by
    rw [hpf, Finset.mem_insert] at h
    exact h.resolve_left hne
  refine ⟨fun q' ↦ if q' = q then _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd hqN) F
      else g' q',
    fun q' hq' ↦ if h : q' = q then h ▸ F else F' q' (hmem hq' h),
    fun q' hq' ↦ if h : q' = q then h ▸ χ₁ else χ'' q' (hmem hq' h), ?_, ?_, ?_, ?_, ?_⟩
  · intro q' hq'
    by_cases h : q' = q
    · subst h
      simp only [↓reduceIte]
      rw [← hχ₁]
      exact CuspForm.ofLe_mem_cuspFormCharSpace χ₁ hqN hF
    · simp only [h, ↓reduceIte]
      exact hg' q' (hmem hq' h)
  · intro q' hq'
    by_cases h : q' = q
    · subst h
      simpa using hF
    · simp only [h, ↓reduceDIte]
      exact hF' q' (hmem hq' h)
  · intro q' hq'
    by_cases h : q' = q
    · subst h
      simp only [↓reduceDIte, ↓reduceIte]
      exact (CuspForm.coe_ofLe _ F).symm
    · simp only [h, ↓reduceDIte, ↓reduceIte]
      exact hF'g' q' (hmem hq' h)
  · intro q' hq'
    by_cases h : q' = q
    · subst h
      simpa using hχ₁
    · simp only [h, ↓reduceDIte]
      exact hχ'' q' (hmem hq' h)
  · intro n
    rw [hcoeff n, hpf, Finset.sum_insert hql']
    simp only [↓reduceIte]
    congr 1
    · rw [CuspForm.coe_ofLe]
    · refine Finset.sum_congr rfl fun q' hq' ↦ ?_
      have hne : q' ≠ q := fun h ↦ hql' (h ▸ hq')
      simp only [hne, ↓reduceIte]

/-- **Peeling a prime off `f`.** The multiples-of-`q` part `h` of `f`, read at level `N q²`
(`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_mul_sq`), is `V_q F` on
coefficients for a form `F` with a nebentypus `χ₁` over `χ`, read at the level `N (q l')² / q`
the decomposition wants. -/
private theorem exists_qExpansion_coeff_eq_ite_coprime_zero_and_ite_dvd {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {q : ℕ}
    (hqp : q.Prime) (l' : ℕ) :
    ∃ (h : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k)
      (F : CuspForm ((Gamma1 (N * (q * l') ^ 2 / q)).map (mapGL ℝ)) k)
      (χ₁ : (ZMod (N * (q * l') ^ 2 / q))ˣ →* ℂˣ),
      h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (q ^ 2)))) ∧
      F ∈ cuspFormCharSpace k χ₁ ∧
      χ₁.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right ((dvd_mul_right q l').trans (dvd_pow_self (q * l') two_ne_zero))
          N))) = χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N ((q * l') ^ 2))) ∧
      (∀ n, (qExpansion 1 h).coeff n = if Nat.Coprime n q then 0 else (qExpansion 1 f).coeff n) ∧
      ∀ n, (qExpansion 1 h).coeff n = if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0 := by
  have : NeZero q := ⟨hqp.ne_zero⟩
  obtain ⟨h, hhχ, hhcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero_mul_sq χ hf (L := q)
  have hNM : N ∣ N * q ^ 2 := Nat.dvd_mul_right N _
  have hNq2q : N * q ^ 2 / q = N * q := by rw [sq, ← mul_assoc, Nat.mul_div_cancel _ hqp.pos]
  obtain ⟨χ₁, F, hF, hχ₁, hFcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd χ hNM
      hqp (dvd_mul_of_dvd_right (dvd_pow_self q two_ne_zero) N)
      (by rw [hNq2q]; exact Nat.dvd_mul_right N q) hhχ (by
        rw [qExpansionSupportedOnDvd_iff, PowerSeries.isSupportedOnDvd_iff]
        intro n hn
        rw [hhcoeff n]
        split_ifs with hc
        · rfl
        · exact absurd (hqp.coprime_iff_not_dvd.mpr hn).symm hc)
  -- `F` read at the level `N (q l')² / q`
  have hdiv : N * q ^ 2 / q ∣ N * (q * l') ^ 2 / q := by
    rw [hNq2q, show N * (q * l') ^ 2 / q = N * q * l' ^ 2 by
      rw [show N * (q * l') ^ 2 = N * q * l' ^ 2 * q by ring, Nat.mul_div_cancel _ hqp.pos]]
    exact dvd_mul_right _ _
  refine ⟨h, _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd hdiv) F,
    χ₁.comp (ZMod.unitsMap hdiv), hhχ, CuspForm.ofLe_mem_cuspFormCharSpace χ₁ hdiv hF, ?_, hhcoeff,
    fun n ↦ by rw [hFcoeff n, CuspForm.coe_ofLe]⟩
  have hNq2 : N * q ^ 2 ∣ N * (q * l') ^ 2 := ⟨l' ^ 2, by ring⟩
  have := congrArg (fun ψ ↦ ψ.comp (ZMod.unitsMap hNq2)) hχ₁
  simp only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] at this ⊢
  exact this

omit [NeZero N] in
/-- **The rest after peeling.** For the multiples-of-`q` part `h` of `f`, the difference
`f' = f - h` at level `N q²` carries the coefficients of `f` at the indices coprime to `q`, so
`a_n(f) = a_n(h) + a_n(f')`. -/
private theorem exists_qExpansion_coeff_eq_ite_coprime_and_add {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {q : ℕ}
    {h : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k}
    (hhχ : h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (q ^ 2)))))
    (hhcoeff : ∀ n, (qExpansion 1 h).coeff n =
      if Nat.Coprime n q then 0 else (qExpansion 1 f).coeff n) :
    ∃ f' : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k,
      f' ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (q ^ 2)))) ∧
      (∀ n, (qExpansion 1 f').coeff n =
        if Nat.Coprime n q then (qExpansion 1 f).coeff n else 0) ∧
      ∀ n, (qExpansion 1 f).coeff n = (qExpansion 1 h).coeff n + (qExpansion 1 f').coeff n := by
  have hNM : N ∣ N * q ^ 2 := Nat.dvd_mul_right N _
  set f' : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k :=
    _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd hNM) f - h with hf'
  have hcoeff (n : ℕ) : (qExpansion 1 f').coeff n =
      if Nat.Coprime n q then (qExpansion 1 f).coeff n else 0 := by
    rw [hf', FunLike.coe_sub,
      _root_.ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub,
      CuspForm.coe_ofLe, hhcoeff n]
    split_ifs <;> simp
  refine ⟨f', Submodule.sub_mem _ (CuspForm.ofLe_mem_cuspFormCharSpace χ hNM hf) hhχ, hcoeff,
    fun n ↦ ?_⟩
  rw [hcoeff n, hhcoeff n]
  split_ifs <;> simp

omit [NeZero N] in
/-- The base case of Lemma 4.6.7, `l = q` prime: the peeled prime is the whole decomposition. -/
private theorem squarefreeDecomposition_prime {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {q : ℕ} (hqp : q.Prime)
    {F : CuspForm ((Gamma1 (N * (q * 1) ^ 2 / q)).map (mapGL ℝ)) k}
    {χ₁ : (ZMod (N * (q * 1) ^ 2 / q))ˣ →* ℂˣ} (hF : F ∈ cuspFormCharSpace k χ₁)
    (hχ₁ : χ₁.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
      (dvd_mul_of_dvd_right ((dvd_mul_right q 1).trans (dvd_pow_self (q * 1) two_ne_zero)) N))) =
      χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N ((q * 1) ^ 2))))
    (hcoeff : ∀ n, (qExpansion 1 f).coeff n =
      if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0) :
    SquarefreeDecomposition χ (q * 1) f := by
  have hempty : ∀ q', q' ∈ Nat.primeFactors 1 → False := fun q' hq' ↦ by
    rw [Nat.primeFactors_one] at hq'
    exact Finset.notMem_empty q' hq'
  refine squarefreeDecomposition_of_insert hqp rfl (fun h ↦ hempty q h) one_ne_zero (fun _ ↦ 0)
    (fun q' hq' ↦ (hempty q' hq').elim) (fun q' hq' ↦ (hempty q' hq').elim)
    (fun q' hq' ↦ (hempty q' hq').elim) (fun q' hq' ↦ (hempty q' hq').elim)
    (fun q' hq' ↦ (hempty q' hq').elim) (fun q' hq' ↦ (hempty q' hq').elim) F χ₁ hF hχ₁ fun n ↦ ?_
  rw [hcoeff n, Nat.primeFactors_one, Finset.sum_empty, add_zero]

/-- The inductive step of Lemma 4.6.7 at `l = q * l'`: peel `q`, apply the induction hypothesis
to the rest at level `N q²` and modulus `l'` (or, when `l' = 1`, nothing remains), and assemble. -/
private theorem squarefreeDecomposition_mul {m : ℕ}
    (ih : ∀ (l : ℕ), l.primeFactors.card = m → ∀ (N : ℕ) [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k), f ∈ cuspFormCharSpace k χ → 1 < l →
      Squarefree l → (∀ n, Nat.Coprime n l → (qExpansion 1 f).coeff n = 0) →
      SquarefreeDecomposition χ l f)
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {q l' : ℕ} (hqp : q.Prime) (hl'0 : l' ≠ 0)
    (hql' : q ∉ l'.primeFactors) (hcard : l'.primeFactors.card = m) (hsq : Squarefree l')
    (hvan : ∀ n, Nat.Coprime n (q * l') → (qExpansion 1 f).coeff n = 0) :
    SquarefreeDecomposition χ (q * l') f := by
  have : NeZero q := ⟨hqp.ne_zero⟩
  obtain ⟨h, F, χ₁, hhχ, hF, hχ₁, hhcoeff, hFcoeff⟩ :=
    exists_qExpansion_coeff_eq_ite_coprime_zero_and_ite_dvd hf hqp l'
  obtain ⟨f', hf'χ, hf'coeff, hsplit⟩ :=
    exists_qExpansion_coeff_eq_ite_coprime_and_add hf hhχ hhcoeff
  have hf'van (n : ℕ) (hn : Nat.Coprime n l') : (qExpansion 1 f').coeff n = 0 := by
    rw [hf'coeff n]
    split_ifs with hnq
    · exact hvan n (Nat.Coprime.mul_right hnq hn)
    · rfl
  by_cases hl'1 : l' = 1
  · -- `l = q` is prime: only the peeled prime contributes
    subst hl'1
    exact squarefreeDecomposition_prime hqp hF hχ₁ fun n ↦ by
      rw [hsplit n, hFcoeff n, hf'van n (Nat.coprime_one_right n), add_zero]
  · -- `l' > 1`: the induction hypothesis applies to `f'` at level `N q²`
    have hl' : 1 < l' := lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hl'0) (Ne.symm hl'1)
    obtain ⟨g', F', χ'', hg', hF', hF'g', hχ'', hcoeff'⟩ :=
      ih l' hcard (N * q ^ 2) (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (q ^ 2)))) f' hf'χ hl'
        hsq hf'van
    have hlev : N * q ^ 2 * l' ^ 2 = N * (q * l') ^ 2 := by ring
    have hlevq (q' : ℕ) : N * q ^ 2 * l' ^ 2 / q' = N * (q * l') ^ 2 / q' := by rw [hlev]
    refine squarefreeDecomposition_of_insert hqp rfl hql' hl'0
      (fun q' ↦ _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_of_eq hlev)) (g' q'))
      (fun q' hq' ↦ _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_of_eq (hlevq q')))
        (F' q' hq'))
      (fun q' hq' ↦ (χ'' q' hq').comp (ZMod.unitsMap (dvd_of_eq (hlevq q')))) ?_ ?_ ?_ ?_ F χ₁ hF
      hχ₁ fun n ↦ ?_
    · intro q' hq'
      have := CuspForm.ofLe_mem_cuspFormCharSpace _ (dvd_of_eq hlev) (hg' q' hq')
      rwa [MonoidHom.comp_assoc, ZMod.unitsMap_comp, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
        at this
    · intro q' hq'
      exact CuspForm.ofLe_mem_cuspFormCharSpace _ _ (hF' q' hq')
    · intro q' hq'
      rw [CuspForm.coe_ofLe, CuspForm.coe_ofLe]
      exact hF'g' q' hq'
    · intro q' hq'
      have := congrArg (fun ψ ↦ ψ.comp (ZMod.unitsMap (dvd_of_eq hlev))) (hχ'' q' hq')
      simp only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] at this ⊢
      exact this
    · rw [hsplit n, hFcoeff n, hcoeff' n]
      congr 1
      exact Finset.sum_congr rfl fun q' _ ↦ by rw [CuspForm.coe_ofLe]

/-- **Miyake's Lemma 4.6.7: the squarefree decomposition.** If `f ∈ S_k(Γ₁(N), χ)` vanishes at
every index coprime to a squarefree `l > 1`, then `a_n(f) = ∑_{q ∣ l, q ∣ n} a_{n/q}(g q)` for
forms `g q ∈ S_k(Γ₁(N l²), χ)`, each the restriction of a form `F q ∈ S_k(Γ₁(N l² / q), χ' q)`
with `χ' q` lying over `χ`: coefficient by coefficient, `f = ∑_{q ∣ l} V_q (F q)`. The proof peels
one prime `q` at a time: the multiples-of-`q` part of `f` is `V_q` of a form of lower level by
`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_qExpansionSupportedOnDvd`, and the
rest vanishes at every index coprime to `l / q`, so induction on the number of primes applies. -/
theorem exists_qExpansion_coeff_eq_sum_primeFactors_of_squarefree (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {l : ℕ}
    (hl : 1 < l) (hsq : Squarefree l)
    (hvan : ∀ n, Nat.Coprime n l → (qExpansion 1 f).coeff n = 0) :
    ∃ (g : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
      (F : ∀ q ∈ l.primeFactors, CuspForm ((Gamma1 (N * l ^ 2 / q)).map (mapGL ℝ)) k)
      (χ' : ∀ q ∈ l.primeFactors, (ZMod (N * l ^ 2 / q))ˣ →* ℂˣ),
      (∀ q ∈ l.primeFactors,
        g q ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2))))) ∧
      (∀ q (hq : q ∈ l.primeFactors), F q hq ∈ cuspFormCharSpace k (χ' q hq)) ∧
      (∀ q (hq : q ∈ l.primeFactors), ⇑(F q hq) = ⇑(g q)) ∧
      (∀ q (hq : q ∈ l.primeFactors),
        (χ' q hq).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
          (dvd_mul_of_dvd_right
            ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_pow_self l two_ne_zero)) N))) =
          χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (l ^ 2)))) ∧
      ∀ n, (qExpansion 1 f).coeff n =
        ∑ q ∈ l.primeFactors, if q ∣ n then (qExpansion 1 (g q)).coeff (n / q) else 0 := by
  suffices key : ∀ (m l : ℕ), l.primeFactors.card = m → ∀ (N : ℕ) [NeZero N]
      (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      f ∈ cuspFormCharSpace k χ → 1 < l → Squarefree l →
      (∀ n, Nat.Coprime n l → (qExpansion 1 f).coeff n = 0) → SquarefreeDecomposition χ l f from
    key _ l rfl N χ f hf hl hsq hvan
  intro m
  induction m with
  | zero =>
    intro l hcard N _ χ f _ hl _ _
    rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hcard) with rfl | rfl <;> omega
  | succ m ih =>
    intro l hcard N _ χ f hf _ hsq hvan
    obtain ⟨q, hq⟩ : l.primeFactors.Nonempty := Finset.card_pos.mp (hcard ▸ Nat.succ_pos m)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    obtain ⟨l', rfl⟩ : ∃ l', l = q * l' := Nat.dvd_of_mem_primeFactors hq
    have hl'0 : l' ≠ 0 := right_ne_zero_of_mul hsq.ne_zero
    have hql' : q ∉ l'.primeFactors := fun h ↦
      (Nat.squarefree_iff_prime_squarefree.mp hsq q hqp)
        (Nat.mul_dvd_mul_left q (Nat.dvd_of_mem_primeFactors h))
    refine squarefreeDecomposition_mul ih hf hqp hl'0 hql' ?_
      (hsq.squarefree_of_dvd (dvd_mul_left l' q)) hvan
    rw [Nat.primeFactors_mul hqp.ne_zero hl'0, hqp.primeFactors, Finset.singleton_union,
      Finset.card_insert_of_notMem hql'] at hcard
    omega

end TauCeti
