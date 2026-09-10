/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Sum

import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The descent slash sum does not see the level away from `p`

The descent family `descendMatrix p N` at a prime `p ∣ N` consists of the `p` upper-triangular
matrices `[1, v; 0, p]`, which do not depend on `N` at all, together with — exactly when
`p² ∤ N` — one extra representative `[1, 0; 0, p] · γ_N`, where `γ_N ∈ SL(2, ℤ)` is chosen
congruent to `S` modulo `p` and to `1` modulo `N / p`. Replacing `N` by `l N` with `l` coprime
to `p` leaves the count unchanged and replaces `γ_N` by some `γ_{lN}`, which satisfies the same
two congruences; so `γ_{lN} γ_N⁻¹` is congruent to `1` modulo `p` and modulo `N / p`, hence
modulo `N`, and conjugating it through `[1, 0; 0, p]` produces an element of `Γ₁(N)`
(`exists_mem_Gamma1_descendMatrix_mul_left_eq`). A function invariant under `Γ₁(N)` therefore
has the same descent slash sum at the two levels (`descendSlash_mul_left_of_coprime`): Miyake's
Lemma 4.6.6, in the form the level-lowering induction consumes.

## Main results

* `TauCeti.descendMatrixCount_mul_left_of_coprime`: the size of the descent family at `l N`
  equals its size at `N` when `l` is coprime to `p`.
* `TauCeti.exists_mem_Gamma1_descendMatrix_mul_left_eq`: the extra representatives at levels
  `l N` and `N` differ on the left by an element of `Γ₁(N)`.
* `TauCeti.descendSlash_mul_left_of_coprime`: **the descent slash sum is the same at levels
  `l N` and `N`** for every function invariant under `Γ₁(N)`.

## Provenance

`descendCosetList_slash_sum_rep_invariance` and `descendCosetList_slash_sum_commute` of the
AINTLIB `LeanModularForms` project (`StrongMultiplicityOne/LevelCommute.lean`, Chris Birkbeck,
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), which assume a
nebentypus; here the invariance is derived from `Γ₁(N)` alone, since the two extra
representatives differ by an element of `Γ(N)` conjugated into `Γ₁(N)`.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.6.
-/

public section

open CongruenceSubgroup HeckeRing.GL2 Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {p l N : ℕ}

/-- The descent family has the same size at `l N` as at `N` when `l` is coprime to `p`. -/
theorem descendMatrixCount_mul_left_of_coprime (hpl : Nat.Coprime p l) (N : ℕ) :
    descendMatrixCount p (l * N) = descendMatrixCount p N := by
  by_cases h : p ^ 2 ∣ N
  · rw [descendMatrixCount_of_sq_dvd h, descendMatrixCount_of_sq_dvd (Dvd.dvd.mul_left h l)]
  · rw [descendMatrixCount_of_not_sq_dvd h, descendMatrixCount_of_not_sq_dvd
      (mt (Nat.Coprime.pow_left 2 hpl).dvd_mul_left.mp h)]

/-- The Chinese remainder theorem for a single integer residue. -/
private theorem intCast_zmod_mul_eq_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) {x y : ℤ}
    (ha : (x : ZMod a) = y) (hb : (x : ZMod b) = y) : (x : ZMod (a * b)) = y := by
  rw [ZMod.intCast_eq_intCast_iff] at ha hb ⊢
  push_cast
  exact (Int.modEq_and_modEq_iff_modEq_mul (by simpa using hab)).mp ⟨ha, hb⟩

/-- `Γ(a) ⊓ Γ(b) ≤ Γ(a b)` for coprime `a` and `b`. -/
private theorem mem_Gamma_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) {γ : SL(2, ℤ)}
    (ha : γ ∈ Gamma a) (hb : γ ∈ Gamma b) : γ ∈ Gamma (a * b) := by
  rw [Gamma_mem] at ha hb ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using intCast_zmod_mul_eq_of_coprime hab (y := 1) (by simpa using ha.1)
      (by simpa using hb.1)
  · simpa using intCast_zmod_mul_eq_of_coprime hab (y := 0) (by simpa using ha.2.1)
      (by simpa using hb.2.1)
  · simpa using intCast_zmod_mul_eq_of_coprime hab (y := 0) (by simpa using ha.2.2.1)
      (by simpa using hb.2.2.1)
  · simpa using intCast_zmod_mul_eq_of_coprime hab (y := 1) (by simpa using ha.2.2.2)
      (by simpa using hb.2.2.2)

/-- The extra matrices at levels `l N` and `N` differ by an element of `Γ(N)`. -/
private theorem descendExtraGamma_mul_inv_mem_Gamma (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) (hpl : Nat.Coprime p l) :
    descendExtraGamma p (l * N) * (descendExtraGamma p N)⁻¹ ∈ Gamma N := by
  have hpN' : p ∣ l * N := Dvd.dvd.mul_left hpN l
  have hpsq' : ¬ p ^ 2 ∣ l * N := mt (Nat.Coprime.pow_left 2 hpl).dvd_mul_left.mp hpsq
  have hcop : Nat.Coprime p (N / p) := hp.coprime_iff_not_dvd.mpr fun h ↦ hpsq <| by
    rw [sq, ← Nat.mul_div_cancel' hpN]
    exact Nat.mul_dvd_mul_left p h
  have hδp : descendExtraGamma p (l * N) * (descendExtraGamma p N)⁻¹ ∈ Gamma p := by
    rw [Gamma_mem', map_mul, map_inv, descendExtraGamma_map_intCast_zmod_eq_S hp hpN' hpsq',
      descendExtraGamma_map_intCast_zmod_eq_S hp hpN hpsq, mul_inv_cancel]
  have hδq : descendExtraGamma p (l * N) * (descendExtraGamma p N)⁻¹ ∈ Gamma (N / p) := by
    have h1 : descendExtraGamma p (l * N) ∈ Gamma (N / p) :=
      Gamma_le_Gamma_of_dvd (by rw [Nat.mul_div_assoc l hpN]; exact dvd_mul_left _ _)
        (Gamma_mem'.mpr (descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN' hpsq'))
    have h2 : descendExtraGamma p N ∈ Gamma (N / p) :=
      Gamma_mem'.mpr (descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq)
    exact (Gamma (N / p)).mul_mem h1 ((Gamma (N / p)).inv_mem h2)
  have := mem_Gamma_mul_of_coprime hcop hδp hδq
  rwa [Nat.mul_div_cancel' hpN] at this

/-- The matrix `[a, b; p c, d]` built from `δ = [a, p b; c, d]`: the conjugate of `δ` through
`[1, 0; 0, p]`, which is again integral of determinant one. -/
private def upperTriConj (p : ℕ) (δ : SL(2, ℤ)) (b : ℤ) (hb : δ 0 1 = p * b) : SL(2, ℤ) :=
  ⟨!![δ 0 0, b; (p : ℤ) * δ 1 0, δ 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination fin_two_mul_sub_mul_eq_one δ + δ 1 0 * hb⟩

private theorem coe_upperTriConj (p : ℕ) (δ : SL(2, ℤ)) (b : ℤ) (hb : δ 0 1 = p * b) :
    (↑(upperTriConj p δ b hb) : Matrix (Fin 2) (Fin 2) ℤ) = !![δ 0 0, b; (p : ℤ) * δ 1 0, δ 1 1] :=
  rfl

/-- Conjugating an element of `Γ(N)` through `[1, 0; 0, p]`, for `p ∣ N`, lands in `Γ₁(N)`:
`[1, 0; 0, p] · δ = ε · [1, 0; 0, p]` with `ε = [a, b / p; p c, d]`. -/
private theorem exists_mem_Gamma1_upperTriRep_mul_mapGL [NeZero p] (hpN : p ∣ N)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma N) :
    ∃ ε ∈ Gamma1 N, upperTriRep p ⟨0, NeZero.pos p⟩ * mapGL ℚ δ =
      mapGL ℚ ε * upperTriRep p ⟨0, NeZero.pos p⟩ := by
  rw [Gamma_mem] at hδ
  obtain ⟨h00, h01, h10, h11⟩ := hδ
  obtain ⟨b, hb⟩ : (p : ℤ) ∣ δ 0 1 :=
    (Int.natCast_dvd_natCast.mpr hpN).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01)
  refine ⟨upperTriConj p δ b hb, ?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [coe_upperTriConj, h00, h10, h11]
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_upperTriRep, coe_mapGL_int_rat_fin_two,
      coe_mapGL_int_rat_fin_two, coe_upperTriConj]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb] <;> ring

/-- **The extra representatives at levels `l N` and `N` differ on the left by `Γ₁(N)`.** -/
theorem exists_mem_Gamma1_descendMatrix_mul_left_eq [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) (hpl : Nat.Coprime p l) {v : Fin (descendMatrixCount p N)}
    (hv : p ≤ v.val) {w : Fin (descendMatrixCount p (l * N))} (hw : p ≤ w.val) :
    ∃ ε ∈ Gamma1 N, descendMatrix p (l * N) w = mapGL ℝ ε * descendMatrix p N v := by
  obtain ⟨ε, hε, hεmul⟩ := exists_mem_Gamma1_upperTriRep_mul_mapGL (p := p) hpN
    (descendExtraGamma_mul_inv_mem_Gamma hp hpN hpsq hpl)
  refine ⟨ε, hε, ?_⟩
  have hQ : upperTriRep p ⟨0, NeZero.pos p⟩ * mapGL ℚ (descendExtraGamma p (l * N)) =
      mapGL ℚ ε * (upperTriRep p ⟨0, NeZero.pos p⟩ * mapGL ℚ (descendExtraGamma p N)) := by
    rw [← mul_assoc, ← hεmul, mul_assoc, ← map_mul, inv_mul_cancel_right]
  simpa only [descendMatrix_of_le hw, descendMatrix_of_le hv, map_mul, map_mapGL]
    using congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hQ

/-- **Miyake, Lemma 4.6.6 — the descent slash sum does not see the level away from `p`.** For
`l` coprime to `p` and `f` invariant under `Γ₁(N)`, the descent slash sums of `f` at levels `l N`
and `N` coincide. -/
theorem descendSlash_mul_left_of_coprime (k : ℤ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    (hpl : Nat.Coprime p l) {f : ℍ → ℂ}
    (hf : ∀ ε ∈ Gamma1 N, f ∣[k] (mapGL ℝ ε : GL (Fin 2) ℝ) = f) :
    descendSlash k p (l * N) f = descendSlash k p N f := by
  rw [descendSlash_def, descendSlash_def]
  refine Fintype.sum_equiv (finCongr (descendMatrixCount_mul_left_of_coprime hpl N)) _ _
    fun w ↦ ?_
  by_cases hw : w.val < p
  · rw [descendMatrix_of_lt hw, descendMatrix_of_lt (v := finCongr _ w) (by simpa using hw)]
    rfl
  · have hpsq : ¬ p ^ 2 ∣ N := fun h ↦ by
      have h1 := w.isLt
      have h2 := descendMatrixCount_mul_left_of_coprime hpl N
      have h3 := descendMatrixCount_of_sq_dvd h
      omega
    obtain ⟨ε, hε, hεeq⟩ := exists_mem_Gamma1_descendMatrix_mul_left_eq hp hpN hpsq hpl
      (v := finCongr (descendMatrixCount_mul_left_of_coprime hpl N) w) (by simpa using hw)
      (Nat.not_lt.mp hw)
    rw [hεeq, SlashAction.slash_mul, hf ε hε]

end TauCeti
