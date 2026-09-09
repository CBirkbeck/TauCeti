/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.CosetDecomposition
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The descent matrices at a prime

Miyake's level descent at a prime `p` runs over the `p` upper-triangular matrices `[1, v; 0, p]`
together with, when `p` divides `N` but `p²` does not, one further matrix built from an element
of `Γ₀(N / p)` reducing to `S = [[0, -1], [1, 0]]` modulo `p` and to the identity modulo `N / p`.
This file supplies that extra matrix, assembles the family of `p` or `p + 1` elements of `GL₂(ℝ)`
the descent runs over, and computes their determinants.

The extra matrix comes from strong approximation at a coprime pair of levels,
`CongruenceSubgroup.exists_mem_Gamma_map_intCast_zmod_eq`: for coprime `d` and `d'` the principal
congruence subgroup `Γ(d')` still surjects onto `SL₂(ℤ/dℤ)`. The descent is that statement at
`d = p` and `d' = N / p` — a coprime pair exactly because `p` divides `N` while `p²` does not —
with `S` as the prescribed reduction modulo `p`. Approximation returns membership in `Γ(N / p)`,
which is stronger than the `Γ₀(N / p)` the descent asks for, so the second reduction is the
identity rather than merely lower-triangular.

## Main definitions

* `TauCeti.descendCosetCount`: the size of the family, `p` when `p² ∣ N` and `p + 1` otherwise.
* `TauCeti.descendExtraGamma`: the extra matrix, with the junk value `1` outside the hypotheses
  that make the choice.
* `TauCeti.descendCosetRep`: the family itself, indexed by `Fin (descendCosetCount p N)`.

## Main results

* `TauCeti.exists_mem_Gamma0_map_intCast_zmod_eq_S`: for a prime `p` with `p ∣ N` and `p² ∤ N`,
  some `γ ∈ Γ₀(N / p)` reduces to `S` modulo `p` and to the identity modulo `N / p`.
* `TauCeti.descendExtraGamma_spec`: those three properties, read back off the chosen matrix.
* `TauCeti.descendCosetCount_of_sq_dvd` and `TauCeti.descendCosetCount_of_not_sq_dvd`: the two
  values of the count.
* `TauCeti.descendCosetRep_of_lt` and `TauCeti.descendCosetRep_of_le`: the two branches of the
  family, as equations in `GL₂(ℝ)`.
* `TauCeti.descendCosetRep_det`: every member of the family has determinant `p`.

## Scope

The family is defined and its determinants computed. That its members *are* a set of coset
representatives, and that the associated slash sum descends the level, are separate statements
about the double coset `Γ₀(N) diag(1, p) Γ₀(N)`; neither is proved here. Until they are, the
family is the intended list of representatives rather than a formalized one.

Follows the AINTLIB `LeanModularForms` project, whose `descendExtraGamma`, `descendCosetCount`,
`descendCosetList` and `descendCosetList_det` are the counterparts of the declarations here, and
specializes its `descendExtraGamma_exists`
(`LeanModularForms/StrongMultiplicityOne/DescentCosets.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), which proves the
same existence directly; here it is read off the general coprime-level statement instead.
-/

public section

open CongruenceSubgroup HeckeRing.GL2

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

/-- **The size of the descent family at `p`.** Miyake's count: `p` when `p²` divides `N`, and
`p + 1` when it does not, the extra member being the one `descendExtraGamma` supplies. -/
def descendCosetCount (p N : ℕ) : ℕ := if p ^ 2 ∣ N then p else p + 1

/-- The descent family has `p` members when `p²` divides `N`. -/
@[simp]
theorem descendCosetCount_of_sq_dvd {p N : ℕ} (h : p ^ 2 ∣ N) : descendCosetCount p N = p := by
  simp [descendCosetCount, h]

/-- The descent family has `p + 1` members when `p²` does not divide `N`. -/
@[simp]
theorem descendCosetCount_of_not_sq_dvd {p N : ℕ} (h : ¬ p ^ 2 ∣ N) :
    descendCosetCount p N = p + 1 := by
  simp [descendCosetCount, h]

/-- **The extra descent matrix.** For a prime `p` exactly dividing `N`, an element of `Γ₀(N / p)`
reducing to `S` modulo `p` and to the identity modulo `N / p`; the junk value `1` when those
hypotheses fail, so that the definition is total. Its three defining properties are
`descendExtraGamma_spec`. -/
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

/-- **The descent family at `p`** (Miyake, Lemma 4.5.11). The `p` upper-triangular matrices
`[1, v; 0, p]` for `v < p`, together with — when `p²` does not divide `N`, so that
`descendCosetCount` is `p + 1` — the further matrix `[1, 0; 0, p] * descendExtraGamma p N`.

Over `ℚ` the upper-triangular part is `HeckeRing.GL2.upperTriRep`, this repository's `T_p`
representative family; the descent family is its image in `GL₂(ℝ)`, where the slash action of a
modular form lives.

`p ∣ N` belongs to the interface rather than to the construction: without it the extra matrix
degenerates to `[1, 0; 0, p]`, which the first branch already lists at `v = 0`. -/
noncomputable def descendCosetRep (p N : ℕ) (hp : p.Prime) (_hpN : p ∣ N) :
    Fin (descendCosetCount p N) → GL (Fin 2) ℝ := fun v ↦
  if h : v.val < p then
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨v.val, h⟩)
  else
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, hp.pos⟩) *
      Matrix.SpecialLinearGroup.mapGL ℝ (descendExtraGamma p N)

/-- The members of the descent family below index `p` are the upper-triangular matrices
`[1, v; 0, p]`. -/
theorem descendCosetRep_of_lt {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    {v : Fin (descendCosetCount p N)} (h : v.val < p) :
    descendCosetRep p N hp hpN v =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨v.val, h⟩) := by
  rw [descendCosetRep]
  split_ifs
  rfl

/-- The member of the descent family at index `p`, present exactly when `p²` does not divide `N`,
is `[1, 0; 0, p]` times the extra matrix. -/
theorem descendCosetRep_of_le {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    {v : Fin (descendCosetCount p N)} (h : p ≤ v.val) :
    descendCosetRep p N hp hpN v =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, hp.pos⟩) *
        Matrix.SpecialLinearGroup.mapGL ℝ (descendExtraGamma p N) := by
  rw [descendCosetRep]
  split_ifs with h'
  · exact absurd h' (Nat.not_lt.mpr h)
  · rfl

/-- **Every member of the descent family has determinant `p`.** This is the determinant condition
cutting out the double coset `Γ₀(N) diag(1, p) Γ₀(N)` that the descent sum runs over. -/
theorem descendCosetRep_det (p N : ℕ) (hp : p.Prime) (hpN : p ∣ N)
    (v : Fin (descendCosetCount p N)) :
    (descendCosetRep p N hp hpN v : Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ) := by
  have hγ : (Matrix.SpecialLinearGroup.mapGL ℝ (descendExtraGamma p N) :
      Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  rw [descendCosetRep]
  split_ifs
  · simp [Matrix.det_fin_two]
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hγ, mul_one]
    simp [Matrix.det_fin_two]

end TauCeti
