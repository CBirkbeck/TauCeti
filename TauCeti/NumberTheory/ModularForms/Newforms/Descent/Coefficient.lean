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

end TauCeti
