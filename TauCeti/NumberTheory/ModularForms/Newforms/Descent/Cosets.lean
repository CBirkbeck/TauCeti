/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The coset representatives of the level descent

Miyake's level descent at a prime `p` uses `p` upper-triangular representatives `[1, v; 0, p]`
and, when `p` divides `N` but `p²` does not, one further representative built from an element of
`Γ₀(N / p)` that reduces to `S = [[0, -1], [1, 0]]` modulo `p` and to the identity modulo `N / p`.
This file supplies that extra matrix, gives the representatives as a list of `p` or `p + 1`
elements of `GL₂(ℝ)`, and computes their determinants.

The matrix comes from strong approximation at a coprime pair of levels,
`CongruenceSubgroup.exists_mem_Gamma_map_intCast_zmod_eq`: for coprime `d` and `d'` the principal
congruence subgroup `Γ(d')` still surjects onto `SL₂(ℤ/dℤ)`. The descent is that statement at
`d = p` and `d' = N / p` — a coprime pair exactly because `p` divides `N` while `p²` does not —
with `S` as the prescribed reduction modulo `p`. Approximation returns membership in `Γ(N / p)`,
which is stronger than the `Γ₀(N / p)` the descent asks for, so the second reduction is the
identity rather than merely lower-triangular.

## Main definitions

* `TauCeti.descendCosetCount`: the number of representatives, `p` when `p² ∣ N` and `p + 1`
  otherwise.
* `TauCeti.descendExtraGamma`: the extra matrix, chosen from the existence statement below, with
  the junk value `1` outside the hypotheses that make the choice.
* `TauCeti.descendCosetList`: the representatives themselves.

## Main results

* `TauCeti.exists_mem_Gamma0_map_intCast_zmod_eq_S`: for a prime `p` with `p ∣ N` and `p² ∤ N`,
  some `γ ∈ Γ₀(N / p)` reduces to `S` modulo `p` and to the identity modulo `N / p`.
* `TauCeti.descendExtraGamma_spec`: those three properties, read back off the chosen matrix.
* `TauCeti.descendCosetList_det`: every representative has determinant `p`.

## Scope

The list is defined and its determinants computed; nothing here proves that these matrices *are*
a set of coset representatives, nor that the associated slash sum descends the level. Those are
separate statements about the double coset `Γ₀(N) diag(1, p) Γ₀(N)`.

Follows `descendExtraGamma`, `descendCosetCount`, `descendCosetList` and `descendCosetList_det`,
and specializes `descendExtraGamma_exists`, of the AINTLIB `LeanModularForms` project
(`LeanModularForms/StrongMultiplicityOne/DescentCosets.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), which proves the
same existence directly; here it is read off the general coprime-level statement instead.
-/

public section

open CongruenceSubgroup

open scoped MatrixGroups

namespace TauCeti

/-- **A matrix with prescribed reductions at `p` and at `N / p`.** For a prime `p` with `p ∣ N` but
`p² ∤ N`, there is a `γ ∈ Γ₀(N / p)` reducing to `S = [[0, -1], [1, 0]]` modulo `p` and to the
identity modulo `N / p`.

`p² ∤ N` is exactly what makes `p` coprime to `N / p`; the target modulo `p` is `S`, and membership
in `Γ₀(N / p)` comes from the stronger `Γ(N / p)` that
`CongruenceSubgroup.exists_mem_Gamma_map_intCast_zmod_eq` already delivers.

This is the matrix Miyake's Lemma 4.5.11 takes as its extra coset representative for the level
descent when `p` exactly divides `N`. Only existence and the two reductions are proved here: the
coset system is not formalized, so nothing is claimed about enumerating or completing it. -/
theorem exists_mem_Gamma0_map_intCast_zmod_eq_S {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) :
    ∃ γ ∈ Gamma0 (N / p),
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) γ =
          Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) ModularGroup.S ∧
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (N / p))) γ = 1 := by
  have hcop : Nat.Coprime p (N / p) := hp.coprime_iff_not_dvd.mpr fun h ↦ hpsq <| by
    have hmul := Nat.mul_dvd_mul_left p h
    rwa [Nat.mul_div_cancel' hpN, ← sq] at hmul
  obtain ⟨γ, hγ, hγp⟩ := exists_mem_Gamma_map_intCast_zmod_eq hcop
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) ModularGroup.S)
  exact ⟨γ, Gamma_le_Gamma0 _ hγ, hγp, Gamma_mem'.mp hγ⟩

/-- **The number of coset representatives for the level descent at `p`.** Miyake's count: `p`
when `p²` divides `N`, and `p + 1` when it does not, the extra representative being the one
`descendExtraGamma` supplies. -/
def descendCosetCount (p N : ℕ) : ℕ := if p ^ 2 ∣ N then p else p + 1

/-- **The extra coset representative.** For a prime `p` exactly dividing `N`, a chosen element
of `Γ₀(N / p)` reducing to `S` modulo `p` and to the identity modulo `N / p`; the junk value `1`
when those hypotheses fail, so that the definition is total.

The choice is made from `exists_mem_Gamma0_map_intCast_zmod_eq_S`, which is the only thing
proved about it; `descendExtraGamma_spec` reads the three properties back off. -/
noncomputable def descendExtraGamma (p N : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  if h : p.Prime ∧ p ∣ N ∧ ¬ p ^ 2 ∣ N then
    (exists_mem_Gamma0_map_intCast_zmod_eq_S h.1 h.2.1 h.2.2).choose
  else 1

/-- **The defining property of `descendExtraGamma`.** Under the hypotheses that make the choice,
it lies in `Γ₀(N / p)`, reduces to `S` modulo `p`, and reduces to the identity modulo `N / p`. -/
theorem descendExtraGamma_spec {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) :
    descendExtraGamma p N ∈ Gamma0 (N / p) ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (descendExtraGamma p N) =
          Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) ModularGroup.S ∧
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (N / p)))
          (descendExtraGamma p N) = 1 := by
  -- `dif_pos` is deprecated on the current pin, so the guard is discharged the way
  -- `TauCeti.diamondOpNat_of_coprime` does it
  have h : descendExtraGamma p N =
      (exists_mem_Gamma0_map_intCast_zmod_eq_S hp hpN hpsq).choose :=
    dite_eq_left_of_eq_true (by simp [hp, hpN, hpsq])
  rw [h]
  exact (exists_mem_Gamma0_map_intCast_zmod_eq_S hp hpN hpsq).choose_spec

/-- **The coset representatives for the level descent at `p`** (Miyake, Lemma 4.5.11). The `p`
upper-triangular matrices `[1, v; 0, p]` for `v < p`, together with — when `p²` does not divide
`N`, so that `descendCosetCount` is `p + 1` — one further representative `[1, 0; 0, p]` times the
matrix `descendExtraGamma` supplies.

Only the list itself is defined here. That these are coset representatives, and that the
associated slash sum descends, are separate statements and are not proved. -/
noncomputable def descendCosetList (p N : ℕ) (hp : p.Prime) :
    Fin (descendCosetCount p N) → GL (Fin 2) ℝ := fun v ↦
  if v.val < p then
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), (v.val : ℝ); 0, (p : ℝ)]
      (by simpa [Matrix.det_fin_two] using (Nat.cast_ne_zero (R := ℝ)).mpr hp.ne_zero)
  else
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
      (by simpa [Matrix.det_fin_two] using (Nat.cast_ne_zero (R := ℝ)).mpr hp.ne_zero) *
      Matrix.SpecialLinearGroup.mapGL ℝ (descendExtraGamma p N)

/-- **Every descent representative has determinant `p`.** The upper-triangular ones by
inspection; the extra one because `descendExtraGamma` has determinant `1`, so multiplying by it
does not change the determinant. -/
theorem descendCosetList_det (p N : ℕ) (hp : p.Prime) (v : Fin (descendCosetCount p N)) :
    (descendCosetList p N hp v : Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ) := by
  rw [descendCosetList]
  split_ifs
  · simp [Matrix.det_fin_two]
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,
      show ((descendExtraGamma p N).val.map (algebraMap ℤ ℝ)).det = 1 by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det,
          (descendExtraGamma p N).property, map_one]]
    simp [Matrix.det_fin_two]

end TauCeti
