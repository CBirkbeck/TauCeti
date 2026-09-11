/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Descent
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CuspForm
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelRaise
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelRaiseCommute
public import TauCeti.NumberTheory.ModularForms.Newforms.SquarefreeDecomposition

/-!
# The coefficients of the descent (work in progress)

For `f ∈ S_k(Γ₁(N), χ)` vanishing at the indices coprime to `p L` and the descended form `g` of
level `L N / p` with `a_m(g) = a_{pm}(f)` at the indices coprime to `L`, the difference
`Δ = f − V_p g` at level `L N` vanishes at every index coprime to `L` and lies in
`S_k(Γ₁(L N), χ ∘ π)`. These are the inputs to the squarefree decomposition of `Δ`, which the
coefficient formula of the descent `a_m(Φ f) = (|family| / p) · a_m(g)` runs on.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N p L : ℕ} {k : ℤ}

/-- **The difference `f − V_p g` vanishes at the indices coprime to `L`.** At `n = p m` both
have the coefficient `a_{pm}(f)`; at `p ∤ n` the index is coprime to `p L`, so `a_n(f) = 0`,
and `V_p g` is supported on the multiples of `p`. -/
theorem qExpansion_coeff_ofLe_sub_levelRaise_eq_zero (hp : p.Prime) (hpN : p ∣ N) [NeZero L]
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0)
    {g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k}
    (hg : ∀ m, (qExpansion 1 g).coeff m =
      if Nat.Coprime m L then (qExpansion 1 f).coeff (p * m) else 0)
    (n : ℕ) (hn : Nat.Coprime n L) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (qExpansion 1 ⇑(_root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left N L)) f -
      CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd
        (dvd_of_eq (Nat.mul_div_cancel' (dvd_mul_of_dvd_right hpN L)))) g)).coeff n = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _),
    map_sub, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
      (one_mem_strictPeriods_Gamma1_map _), _root_.CuspForm.coe_ofLe]
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    rw [ite_eq_left (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.pos, hg,
      ite_eq_left (Nat.coprime_mul_iff_left.mp hn).2, sub_self]
  · simp only [hpn, ↓reduceIte, sub_zero]
    exact hvan n (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hpn).symm hn)

/-- **The difference `f − V_p g` has the nebentypus of `f`, read at level `L N`.** -/
theorem ofLe_sub_levelRaise_mem_cuspFormCharSpace (hp : p.Prime) (hpN : p ∣ N) [NeZero L]
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    {g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k}
    (hg : g ∈ cuspFormCharSpace k
      (χ₀.comp (ZMod.unitsMap (Nat.mul_div_assoc L hpN ▸ dvd_mul_left (N / p) L)))) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left N L)) f -
      CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd
        (dvd_of_eq (Nat.mul_div_cancel' (dvd_mul_of_dvd_right hpN L)))) g ∈
      cuspFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_mul_left N L))) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine Submodule.sub_mem _ (CuspForm.ofLe_mem_cuspFormCharSpace χ (dvd_mul_left N L) hf) ?_
  have h := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd
    (dvd_of_eq (Nat.mul_div_cancel' (dvd_mul_of_dvd_right hpN L))) _ hg
  rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp] at h
  rwa [hcomp, MonoidHom.comp_assoc, ZMod.unitsMap_comp]

/-! ### The descent of the difference vanishes at the indices coprime to `L` -/

section Core

variable {M : ℕ}

/-- The `m`-th coefficient of a finite sum of cusp forms of level `Γ₁(M)`. -/
private theorem qExpansion_coeff_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 ⇑(∑ i ∈ s, F i : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)).coeff m =
      ∑ i ∈ s, (qExpansion 1 (F i)).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, FunLike.coe_zero, qExpansion_zero, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, FunLike.coe_add,
      ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1_map _), map_add, ih]

/-- **A character over a lowered character is lowered.** If `χ'` modulo `N'` and `χ₀ ∘ π` modulo
`M` have the same pull-back to a common multiple `M'`, where `χ₀` has level `M / p` and
`M ∣ N'`, then `χ'` is the pull-back of `χ₀ ∘ π` modulo `N' / p`: the pull-back to `M'` is
injective on characters, by the surjectivity of `ZMod.unitsMap`. -/
private theorem eq_comp_unitsMap_of_comp_unitsMap_eq {M' N' : ℕ} [NeZero M'] (hpM : p ∣ M)
    (hpN' : p ∣ N') (hMpN'p : M / p ∣ N' / p) (hMN' : M ∣ N') (hN'M' : N' ∣ M')
    {χM : (ZMod M)ˣ →* ℂˣ} {χ₀ : (ZMod (M / p))ˣ →* ℂˣ}
    (hcomp : χM = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) {χ' : (ZMod N')ˣ →* ℂˣ}
    (h : χ'.comp (ZMod.unitsMap hN'M') = χM.comp (ZMod.unitsMap (hMN'.trans hN'M'))) :
    χ' = (χ₀.comp (ZMod.unitsMap hMpN'p)).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN')) := by
  rw [hcomp, MonoidHom.comp_assoc, ZMod.unitsMap_comp] at h
  refine MonoidHom.ext fun u ↦ ?_
  obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hN'M' u
  have hv := congrArg (fun ψ ↦ ψ v) h
  simp only [MonoidHom.comp_apply] at hv ⊢
  rw [hv, ← MonoidHom.comp_apply (ZMod.unitsMap _) (ZMod.unitsMap _), ZMod.unitsMap_comp,
    ← MonoidHom.comp_apply (ZMod.unitsMap _) (ZMod.unitsMap _), ZMod.unitsMap_comp]

/-- **A peeled summand descends to a level-raise of a bundled descent.** For `F` of level
`Γ₁(M l² / q)` with a nebentypus lying over the lowered one, the descent at level `M l²` of the
function `V_q F` is `V_q` of the descent of `F`, bundled at level `Γ₁(M l² / p)`:
`descendSlash_coe_levelRaise_mul_left` read through `descendCuspForm`. -/
private theorem descendSlash_smul_slash_scaleGL_eq_coe_levelRaise (hp : p.Prime) {l q : ℕ}
    (hpM : p ∣ M) (hq : q.Prime) (hql : q ∣ l) (hpl : Nat.Coprime p l)
    [NeZero (M * l ^ 2 / q)] (hpN' : p ∣ M * l ^ 2 / q) (hMN' : M ∣ M * l ^ 2 / q)
    (hle : q * (M * l ^ 2 / q / p) ∣ M * l ^ 2 / p)
    {χM : (ZMod M)ˣ →* ℂˣ} {χ₀ : (ZMod (M / p))ˣ →* ℂˣ}
    (hcomp : χM = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))
    {χ' : (ZMod (M * l ^ 2 / q))ˣ →* ℂˣ}
    (hχ' : χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right (hql.trans (dvd_pow_self l two_ne_zero)) M))) =
      χM.comp (ZMod.unitsMap (Nat.dvd_mul_right M (l ^ 2))))
    {F : CuspForm ((Gamma1 (M * l ^ 2 / q)).map (mapGL ℝ)) k} (hF : F ∈ cuspFormCharSpace k χ') :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ∃ hcomp' : χ' = (χ₀.comp (ZMod.unitsMap ((Nat.div_dvd_div_iff_right hpM hpN').mpr
        hMN'))).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN')),
      descendSlash k p (M * l ^ 2) ((q : ℂ) ^ (1 - k) • (⇑F ∣[k] scaleGL q)) =
        ⇑(CuspForm.levelRaise q (Gamma1_map_le_conjAct_scaleGL_of_dvd hle)
          (descendCuspForm k hp hpN' hcomp' hF)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  have hqMl : q ∣ M * l ^ 2 := dvd_mul_of_dvd_right (hql.trans (dvd_pow_self l two_ne_zero)) M
  have : NeZero (M * l ^ 2) := ⟨fun h ↦ NeZero.ne (M * l ^ 2 / q) (by rw [h, Nat.zero_div])⟩
  have hcomp' := eq_comp_unitsMap_of_comp_unitsMap_eq hpM hpN'
    ((Nat.div_dvd_div_iff_right hpM hpN').mpr hMN') hMN' (Nat.div_dvd_of_dvd hqMl) hcomp hχ'
  refine ⟨hcomp', ?_⟩
  have h := descendSlash_coe_levelRaise_mul_left k hp hpN' (hpl.coprime_dvd_right hql) hcomp' hF
  rw [CuspForm.coe_levelRaise, Nat.mul_div_cancel' hqMl] at h
  rw [h, CuspForm.coe_levelRaise, coe_descendCuspForm]

end Core

end TauCeti
