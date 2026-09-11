/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelCommute
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Sum

/-!
# The descent commutes with the level-raise

Miyake's Lemma 4.6.6 (2): for a prime `p ∣ N` and `l` coprime to `p`, the descent slash sum at
level `l N` of the level-raise `V_l f` of `f ∈ S_k(Γ₁(N), χ)` is the level-raise of the descent
slash sum of `f` at level `N`, provided `χ` is the pull-back of a character modulo `N / p`. The
upper-triangular members `!![1, b; 0, p]` of the two families are
matched by the permutation `b ↦ l b mod p` of the residues, and the extra members (present when
`p² ∤ N`) by conjugating the level-`l N` one back to level `N`, where the nebentypus shows the
two candidates give the same slash.

## Main results

* `TauCeti.descendSlash_coe_levelRaise_mul_left`: `descendSlash k p (l N) (V_l f) =
  l ^ (1 - k) • (descendSlash k p N f ∣[k] diag(l, 1))`, that is, `V_l` of the descent.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/LevelCommute.lean`
(`level_commute_delta` and its `delta_*` helpers, `descendCosetList_slash_sum_rep_invariance`,
`extra_rep_levelRaise_bridge`). The source's `modularFormLevelRaise` is this repository's
`CuspForm.levelRaise`, its `levelRaiseConjOfDvd` is `conjScale`, and its explicit coset list is
the family `descendMatrix`; the statements are re-proved on those.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {p l : ℕ} (k : ℤ)

/-- Multiplication by `l` coprime to the prime `p` permutes the residues modulo `p`. -/
private theorem bijective_mulMod (hp : p.Prime) (hpl : Nat.Coprime p l) :
    Function.Bijective fun b : Fin p ↦ (⟨l * b % p, Nat.mod_lt _ hp.pos⟩ : Fin p) := by
  have : Fact p.Prime := ⟨hp⟩
  refine Finite.injective_iff_bijective.mp fun a b hab ↦ ?_
  have hl : (l : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp hpl
  have h : ((l * a % p : ℕ) : ZMod p) = ((l * b % p : ℕ) : ZMod p) :=
    congrArg (fun x : Fin p ↦ ((x : ℕ) : ZMod p)) hab
  rw [ZMod.natCast_mod, ZMod.natCast_mod] at h
  push_cast at h
  exact Fin.ext (by
    rw [← ZMod.val_natCast_of_lt a.isLt, ← ZMod.val_natCast_of_lt b.isLt,
      mul_left_cancel₀ hl h])

/-- **An upper-triangular member of the family, after the level-raise.** For `f` of level `Γ₁(M)`,
`(V_l f) ∣[k] !![1, b; 0, p]` is `V_l` of `f ∣[k] !![1, l b mod p; 0, p]`, because the points
`l (τ + b) / p` and `(l τ + (l b mod p)) / p` differ by the integer `l b div p`. -/
private theorem coe_levelRaise_slash_upperTriRep_eq_smul_slash {M : ℕ} (hp : p.Prime)
    [NeZero l] (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (b : Fin p) :
    ⇑(CuspForm.levelRaise l (Gamma1_map_le_conjAct_scaleGL M l) f) ∣[k]
        (upperTriRep p b : GL (Fin 2) ℚ) =
      (l : ℂ) ^ (1 - k) •
        ((⇑f ∣[k] (upperTriRep p ⟨l * b % p, Nat.mod_lt _ hp.pos⟩ : GL (Fin 2) ℚ)) ∣[k]
          scaleGL l) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  funext τ
  rw [slash_upperTriRep_apply, CuspForm.levelRaise_apply, Pi.smul_apply, slash_scaleGL_apply,
    slash_upperTriRep_apply, smul_eq_mul]
  have hpt : scaleGL l • (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p b) • τ) =
      ((l * b / p : ℕ) : ℝ) +ᵥ (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (upperTriRep p ⟨l * b % p, Nat.mod_lt _ hp.pos⟩) • (scaleGL l • τ)) := by
    ext1
    rw [coe_scaleGL_smul, coe_upperTriRep_smul, UpperHalfPlane.coe_vadd, coe_upperTriRep_smul,
      coe_scaleGL_smul]
    have hC : (l : ℂ) * b = p * (l * b / p : ℕ) + (l * b % p : ℕ) := by
      exact_mod_cast (Nat.div_add_mod (l * b) p).symm
    push_cast
    field_simp
    linear_combination hC
  rw [hpt, SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f _
    (by simpa using AddSubgroup.nsmul_mem _ (one_mem_strictPeriods_Gamma1_map M) (l * b / p)),
    ← mul_assoc, ← zpow_add₀ hl0, show 1 - k + (k - 1) = 0 by ring, zpow_zero, one_mul]

/-- `diag(l, 1)` and `!![1, 0; 0, p]` commute. -/
private theorem scaleGL_mul_map_upperTriRep_zero [NeZero p] [NeZero l] :
    scaleGL l * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) *
        scaleGL l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, coe_scaleGL]

/-- The integral matrix conjugate to `δ` across `!![1, 0; 0, p]`, when `p` divides the upper-right
entry `δ 0 1 = p * b`: the upper-right entry divided by `p`, the lower-left one multiplied by
`p`. -/
private def conjUpper (δ : SL(2, ℤ)) (b : ℤ) (hb : δ 0 1 = p * b) : SL(2, ℤ) :=
  ⟨!![δ 0 0, b; (p : ℤ) * δ 1 0, δ 1 1], by
    have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 :=
      Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one δ
    rw [Matrix.det_fin_two_of]
    rw [hb] at hdet
    linear_combination hdet⟩

private lemma coe_conjUpper (δ : SL(2, ℤ)) (b : ℤ) (hb : δ 0 1 = p * b) :
    ((conjUpper δ b hb : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![δ 0 0, b; (p : ℤ) * δ 1 0, δ 1 1] :=
  rfl

/-- **Conjugating across `!![1, 0; 0, p]`**: `!![1, 0; 0, p] · δ = conjUpper δ b · !![1, 0; 0, p]`
when `δ 0 1 = p * b`. -/
private theorem map_upperTriRep_zero_mul_mapGL [NeZero p] (δ : SL(2, ℤ)) {b : ℤ}
    (hb : δ 0 1 = p * b) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) *
        mapGL ℝ δ =
      mapGL ℝ (conjUpper δ b hb) *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) := by
  have hbR : ((δ 0 1 : ℤ) : ℝ) = p * (b : ℝ) := by exact_mod_cast hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.map_apply, Matrix.mul_apply,
      Fin.sum_univ_two, coe_conjUpper, hbR, mul_comm]

/-- The level-`l N` extra matrix modulo `N / p`: its diagonal entries are `1`, and `c`, the
lower-left entry divided by `l`, is `0`. -/
private theorem descendExtraGamma_mul_left_mod_div {N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) [NeZero l] (hpl : Nat.Coprime p l) {c : ℤ}
    (hc : descendExtraGamma p (l * N) 1 0 = l * c) :
    ((descendExtraGamma p (l * N) 0 0 : ℤ) : ZMod (N / p)) = 1 ∧
      ((descendExtraGamma p (l * N) 1 1 : ℤ) : ZMod (N / p)) = 1 ∧
        ((c : ℤ) : ZMod (N / p)) = 0 := by
  have hplN : p ∣ l * N := dvd_mul_of_dvd_right hpN l
  have hpsq' : ¬ p ^ 2 ∣ l * N := fun h ↦
    hpsq ((Nat.Coprime.pow_left 2 hpl).dvd_of_dvd_mul_left h)
  have hNlN : N / p ∣ l * N / p := by
    rw [Nat.mul_div_assoc l hpN]
    exact dvd_mul_left _ _
  have m₁ (i j : Fin 2) : ((descendExtraGamma p (l * N) i j : ℤ) : ZMod (l * N / p)) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod (l * N / p))) i j := by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast,
      Matrix.SpecialLinearGroup.coe_one] using
      congr_fun₂ (congrArg Subtype.val
        (descendExtraGamma_map_intCast_zmod_div_eq_one hp hplN hpsq')) i j
  have m₁' (i j : Fin 2) : ((descendExtraGamma p (l * N) i j : ℤ) : ZMod (N / p)) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod (N / p))) i j := by
    have := congrArg (ZMod.castHom hNlN (ZMod (N / p))) (m₁ i j)
    rw [map_intCast] at this
    rw [this]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
  refine ⟨by rw [m₁' 0 0, Matrix.one_apply_eq], by rw [m₁' 1 1, Matrix.one_apply_eq], ?_⟩
  have h10 : ((l * N / p : ℕ) : ℤ) ∣ l * c := by
    rw [← hc]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (by rw [m₁ 1 0]; exact Matrix.one_apply_ne (by decide))
  rw [Nat.mul_div_assoc l hpN] at h10
  push_cast at h10
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    ((mul_dvd_mul_iff_left (Nat.cast_ne_zero.mpr (NeZero.ne l))).mp h10)

/-- The entries of the quotient of the conjugated level-`l N` extra matrix by the level-`N` one
that the residue computations read. -/
private theorem conjScale_descendExtraGamma_mul_inv_apply {N : ℕ} {c : ℤ}
    (hc : descendExtraGamma p (l * N) 1 0 = l * c) :
    (conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 0 1 =
        descendExtraGamma p (l * N) 0 0 * (-descendExtraGamma p N 0 1) +
          (l : ℤ) * descendExtraGamma p (l * N) 0 1 * descendExtraGamma p N 0 0 ∧
      (conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 1 0 =
        c * descendExtraGamma p N 1 1 +
          descendExtraGamma p (l * N) 1 1 * (-descendExtraGamma p N 1 0) ∧
      (conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 1 1 =
        c * (-descendExtraGamma p N 0 1) +
          descendExtraGamma p (l * N) 1 1 * descendExtraGamma p N 0 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, coe_conjScale, Matrix.mul_apply, Fin.sum_univ_two]

/-- The quotient of the conjugated level-`l N` extra matrix by the level-`N` one is diagonal
modulo `p` (its upper-right entry vanishes) and is `1` modulo `N / p`. -/
private theorem conjScale_descendExtraGamma_mul_inv_mod {N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) [NeZero l] (hpl : Nat.Coprime p l) {c : ℤ}
    (hc : descendExtraGamma p (l * N) 1 0 = l * c) :
    (((conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 0 1 : ℤ) :
        ZMod p) = 0 ∧
      (((conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) :
        ZMod (N / p)) = 0 ∧
      (((conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 1 1 : ℤ) :
        ZMod (N / p)) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hplN : p ∣ l * N := dvd_mul_of_dvd_right hpN l
  have hpsq' : ¬ p ^ 2 ∣ l * N := fun h ↦
    hpsq ((Nat.Coprime.pow_left 2 hpl).dvd_of_dvd_mul_left h)
  obtain ⟨h00, h11, hcN⟩ := descendExtraGamma_mul_left_mod_div hp hpN hpsq hpl hc
  have e₁ (i j : Fin 2) : ((descendExtraGamma p (l * N) i j : ℤ) : ZMod p) =
      ((ModularGroup.S i j : ℤ) : ZMod p) := by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
      congr_fun₂ (congrArg Subtype.val (descendExtraGamma_map_intCast_zmod_eq_S hp hplN hpsq'))
        i j
  have e₂ (i j : Fin 2) : ((descendExtraGamma p N i j : ℤ) : ZMod p) =
      ((ModularGroup.S i j : ℤ) : ZMod p) := by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
      congr_fun₂ (congrArg Subtype.val (descendExtraGamma_map_intCast_zmod_eq_S hp hpN hpsq)) i j
  have m₂ (i j : Fin 2) : ((descendExtraGamma p N i j : ℤ) : ZMod (N / p)) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod (N / p))) i j := by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast,
      Matrix.SpecialLinearGroup.coe_one] using
      congr_fun₂ (congrArg Subtype.val (descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq))
        i j
  obtain ⟨d01, d10, d11⟩ := conjScale_descendExtraGamma_mul_inv_apply (N := N) hc
  refine ⟨?_, ?_, ?_⟩
  · rw [d01]
    push_cast
    rw [e₁ 0 0, e₂ 0 0]
    simp [ModularGroup.coe_S]
  · rw [d10]
    push_cast
    rw [hcN, h11, m₂ 1 0, Matrix.one_apply_ne (by decide)]
    ring
  · rw [d11]
    push_cast
    rw [hcN, h11, m₂ 0 0, Matrix.one_apply_eq]
    ring

/-- A matrix of `Γ₀(N)` whose lower-right entry is `1` modulo `N / p` acts trivially on
`f ∈ S_k(Γ₁(N), χ)` when `χ` is pulled back from a character modulo `N / p`. -/
private theorem slash_mapGL_eq_self_of_mem_Gamma0_of_mod_div {N : ℕ} (hpN : p ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {β : SL(2, ℤ)}
    (hβ : β ∈ Gamma0 N) (hβ11 : ((β 1 1 : ℤ) : ZMod (N / p)) = 1) :
    ⇑f ∣[k] mapGL ℝ β = ⇑f := by
  rw [(mem_cuspFormCharSpace_iff_nebentypus k χ f).mp hf ⟨β, hβ⟩, hcomp, MonoidHom.comp_apply,
    ← Gamma0Map_toHomUnits_of_dvd (Nat.div_dvd_of_dvd hpN) ⟨β, hβ⟩
      (Gamma0_le_Gamma0_of_dvd (Nat.div_dvd_of_dvd hpN) hβ)]
  have h1 : (Gamma0Map (N / p)).toHomUnits
      ⟨β, Gamma0_le_Gamma0_of_dvd (Nat.div_dvd_of_dvd hpN) hβ⟩ = 1 := by
    refine Units.ext ?_
    rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply]
    exact hβ11
  rw [h1, map_one, Units.val_one, one_smul]

/-- **The two extra members give the same slash.** For `p ∥ N`, `l` coprime to `p`, and
`f ∈ S_k(Γ₁(N), χ)` with `χ` pulled back from `χ₀` modulo `N / p`: conjugating the level-`l N`
extra matrix `descendExtraGamma p (l N)` back to level `N` by `diag(l, 1)`, then slashing `f` by
`!![1, 0; 0, p]` times it, is the same as with the level-`N` extra matrix `descendExtraGamma p N`.
The quotient `δ` of the two candidates is `1` modulo `N / p` and diagonal modulo `p`, so
`!![1, 0; 0, p] δ = β !![1, 0; 0, p]` with `β ∈ Γ₀(N)` of lower-right entry `1` modulo `N / p`, on
which the nebentypus is trivial. -/
private theorem slash_map_upperTriRep_zero_mul_mapGL_conjScale_eq {N : ℕ} [NeZero N]
    (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) [NeZero l] (hpl : Nat.Coprime p l)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {c : ℤ}
    (hc : descendExtraGamma p (l * N) 1 0 = l * c) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ⇑f ∣[k] (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) *
        mapGL ℝ (conjScale l (descendExtraGamma p (l * N)) c hc)) =
      ⇑f ∣[k] (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) *
        mapGL ℝ (descendExtraGamma p N)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  set δ : SL(2, ℤ) := conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹
    with hδ
  obtain ⟨hδ01, hδ10, hδ11⟩ := conjScale_descendExtraGamma_mul_inv_mod hp hpN hpsq hpl hc
  obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ01
  -- the conjugate `β` lies in `Γ₀(N)` with lower-right entry `1` modulo `N / p`
  have hβ : conjUpper δ b hb ∈ Gamma0 N := by
    rw [Gamma0_mem, show (conjUpper δ b hb) 1 0 = p * δ 1 0 by simp [coe_conjUpper]]
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ10
    have hpN' : ((p : ℤ) * ((N / p : ℕ) : ℤ)) = (N : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hpN
    rw [ht, ← mul_assoc, hpN']
    simp
  have hfβ : ⇑f ∣[k] mapGL ℝ (conjUpper δ b hb) = ⇑f :=
    slash_mapGL_eq_self_of_mem_Gamma0_of_mod_div k hpN hcomp hf hβ (by
      rw [show (conjUpper δ b hb) 1 1 = δ 1 1 by simp [coe_conjUpper]]
      exact hδ11)
  have hδγ : conjScale l (descendExtraGamma p (l * N)) c hc = δ * descendExtraGamma p N := by
    rw [hδ, inv_mul_cancel_right]
  rw [hδγ, map_mul, ← mul_assoc, map_upperTriRep_zero_mul_mapGL δ hb, mul_assoc,
    SlashAction.slash_mul, hfβ]

/-- The index map between the two descent families: multiplication by `l` on the residues modulo
`p`, the identity on the extra index. -/
private def descendIndexMul (hp : p.Prime) (hpl : Nat.Coprime p l) (N : ℕ)
    (v : Fin (descendMatrixCount p (l * N))) : Fin (descendMatrixCount p N) :=
  if h : v.val < p then
    ⟨l * v % p, lt_of_lt_of_le (Nat.mod_lt _ hp.pos) (by
      by_cases h' : p ^ 2 ∣ N
      · rw [descendMatrixCount_of_sq_dvd h']
      · rw [descendMatrixCount_of_not_sq_dvd h']
        exact Nat.le_succ p)⟩
  else ⟨v.val, lt_of_lt_of_eq v.isLt (descendMatrixCount_mul_left_of_coprime hpl N)⟩

private theorem descendIndexMul_of_lt (hp : p.Prime) (hpl : Nat.Coprime p l) (N : ℕ)
    {v : Fin (descendMatrixCount p (l * N))} (hv : v.val < p) :
    (descendIndexMul hp hpl N v).val = l * v % p := by
  simp [descendIndexMul, hv]

private theorem descendIndexMul_of_le (hp : p.Prime) (hpl : Nat.Coprime p l) (N : ℕ)
    {v : Fin (descendMatrixCount p (l * N))} (hv : p ≤ v.val) :
    (descendIndexMul hp hpl N v).val = v.val := by
  simp [descendIndexMul, not_lt.mpr hv]

private theorem descendIndexMul_bijective (hp : p.Prime) (hpl : Nat.Coprime p l) (N : ℕ) :
    Function.Bijective (descendIndexMul hp hpl N) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun v w hvw ↦ ?_,
    by simp [descendMatrixCount_mul_left_of_coprime hpl N]⟩
  have hvw' := congrArg Fin.val hvw
  rcases lt_or_ge v.val p with hv | hv <;> rcases lt_or_ge w.val p with hw | hw
  · rw [descendIndexMul_of_lt hp hpl N hv, descendIndexMul_of_lt hp hpl N hw] at hvw'
    have := (bijective_mulMod hp hpl).1 (a₁ := ⟨v.val, hv⟩) (a₂ := ⟨w.val, hw⟩) (Fin.ext hvw')
    exact Fin.ext (Fin.mk.inj_iff.mp this)
  · rw [descendIndexMul_of_lt hp hpl N hv, descendIndexMul_of_le hp hpl N hw] at hvw'
    exact absurd (hvw' ▸ Nat.mod_lt (l * v.val) hp.pos) (not_lt.mpr hw)
  · rw [descendIndexMul_of_le hp hpl N hv, descendIndexMul_of_lt hp hpl N hw] at hvw'
    exact absurd (hvw' ▸ Nat.mod_lt (l * w.val) hp.pos) (not_lt.mpr hv)
  · rw [descendIndexMul_of_le hp hpl N hv, descendIndexMul_of_le hp hpl N hw] at hvw'
    exact Fin.ext hvw'

/-- An upper-triangular member of the level-`l N` family, on `V_l f`, is `V_l` of the matching
member of the level-`N` family on `f`. -/
private theorem coe_levelRaise_slash_descendMatrix_of_lt {N : ℕ} (hp : p.Prime)
    (hpl : Nat.Coprime p l) [NeZero l] (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {v : Fin (descendMatrixCount p (l * N))} (hv : v.val < p) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ⇑(CuspForm.levelRaise l (Gamma1_map_le_conjAct_scaleGL N l) f) ∣[k]
        descendMatrix p (l * N) v =
      (l : ℂ) ^ (1 - k) •
        ((⇑f ∣[k] descendMatrix p N (descendIndexMul hp hpl N v)) ∣[k] scaleGL l) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hσ : (descendIndexMul hp hpl N v).val < p :=
    (descendIndexMul_of_lt hp hpl N hv).symm ▸ Nat.mod_lt _ hp.pos
  rw [descendMatrix_of_lt hv, descendMatrix_of_lt hσ, ← ModularForm.rat_slash,
    ← ModularForm.rat_slash, coe_levelRaise_slash_upperTriRep_eq_smul_slash k hp f ⟨v.val, hv⟩]
  congr 4
  exact Fin.ext (descendIndexMul_of_lt hp hpl N hv).symm

/-- The extra member of the level-`l N` family, on `V_l f`, is `V_l` of the extra member of the
level-`N` family on `f`. -/
private theorem coe_levelRaise_slash_descendMatrix_of_le {N : ℕ} [NeZero N] (hp : p.Prime)
    (hpN : p ∣ N) [NeZero l] (hpl : Nat.Coprime p l) {χ : (ZMod N)ˣ →* ℂˣ}
    {χ₀ : (ZMod (N / p))ˣ →* ℂˣ} (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    {v : Fin (descendMatrixCount p (l * N))} (hv : p ≤ v.val) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ⇑(CuspForm.levelRaise l (Gamma1_map_le_conjAct_scaleGL N l) f) ∣[k]
        descendMatrix p (l * N) v =
      (l : ℂ) ^ (1 - k) •
        ((⇑f ∣[k] descendMatrix p N (descendIndexMul hp hpl N v)) ∣[k] scaleGL l) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpsq : ¬ p ^ 2 ∣ N := fun h ↦ by
    have h1 := descendMatrixCount_of_sq_dvd h
    have h2 := lt_of_lt_of_eq v.isLt (descendMatrixCount_mul_left_of_coprime hpl N)
    omega
  have hplN : p ∣ l * N := dvd_mul_of_dvd_right hpN l
  have hpsq' : ¬ p ^ 2 ∣ l * N := fun h ↦
    hpsq ((Nat.Coprime.pow_left 2 hpl).dvd_of_dvd_mul_left h)
  obtain ⟨c, hc⟩ : (l : ℤ) ∣ descendExtraGamma p (l * N) 1 0 := by
    refine (Int.natCast_dvd_natCast.mpr ?_ : (l : ℤ) ∣ ((l * N / p : ℕ) : ℤ)).trans
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        (Gamma0_mem.mp (descendExtraGamma_mem_Gamma0 hp hplN hpsq')))
    rw [Nat.mul_div_assoc l hpN]
    exact dvd_mul_right l _
  rw [CuspForm.coe_levelRaise,
    ModularForm.smul_slash_of_det_pos k (descendMatrix_det_pos p (l * N) v),
    descendMatrix_eq_map, descendMatrixRat_of_le hv, descendMatrix_eq_map,
    descendMatrixRat_of_le ((descendIndexMul_of_le hp hpl N hv).symm ▸ hv), map_mul, map_mul,
    map_mapGL, map_mapGL, ← SlashAction.slash_mul, ← mul_assoc, scaleGL_mul_map_upperTriRep_zero,
    mul_assoc, mul_inv_eq_iff_eq_mul.mp (mapGL_conjScale (descendExtraGamma p (l * N)) c hc),
    ← mul_assoc, SlashAction.slash_mul,
    slash_map_upperTriRep_zero_mul_mapGL_conjScale_eq k hp hpN hpsq hpl hcomp hf hc]

/-- **The descent commutes with the level-raise** (Miyake, Lemma 4.6.6 (2)). For a prime `p ∣ N`,
`l` coprime to `p`, and `f ∈ S_k(Γ₁(N), χ)` with `χ` the pull-back of a character modulo `N / p`,
the descent slash sum at level `l N` of `V_l f` is `V_l` of the descent slash sum of `f` at level
`N`: `descendSlash k p (l N) (V_l f) = l ^ (1 - k) • (descendSlash k p N f ∣[k] diag(l, 1))`.
The source needs `l ∣ N / p` as well; here it is not used. -/
theorem descendSlash_coe_levelRaise_mul_left {N : ℕ} [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    [NeZero l] (hpl : Nat.Coprime p l) {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    descendSlash k p (l * N) ⇑(CuspForm.levelRaise l (Gamma1_map_le_conjAct_scaleGL N l) f) =
      (l : ℂ) ^ (1 - k) • (descendSlash k p N ⇑f ∣[k] scaleGL l) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [descendSlash_def, descendSlash_def, SlashAction.sum_slash, Finset.smul_sum]
  refine Fintype.sum_bijective _ (descendIndexMul_bijective hp hpl N) _ _ fun v ↦ ?_
  rcases lt_or_ge v.val p with hv | hv
  · exact coe_levelRaise_slash_descendMatrix_of_lt k hp hpl f hv
  · exact coe_levelRaise_slash_descendMatrix_of_le k hp hpN hpl hcomp hf hv

end TauCeti
