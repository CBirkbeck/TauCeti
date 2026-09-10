/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MoebiusZMod
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.UpperTriFactorization
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Cosets

/-!
# The level-descent matrices are permuted by `Γ₀(N / p)` when `p` exactly divides `N`

`Newforms/Descent/Action.lean` proves that, at a prime with `p² ∣ N`, right multiplication by
`γ ∈ Γ₀(N / p)` permutes the descent family `descendMatrix p N` up to `Γ₀(N)`. This file proves
the same when `p` exactly divides `N`, where the family has one further member,
`[1, 0; 0, p] γ_p` for the extra matrix `γ_p = descendExtraGamma p N`, and `γ` no longer lies
in `Γ₀(p)`.

## The index line

With `p + 1` members the natural index set is the projective line over `ZMod p`: the
upper-triangular member `[1, j; 0, p]` sits at the affine point `j`, the extra member at `∞`
(`descendIndexEquiv`). On that line the descent's index map `j ↦ (b + j d) / (a + j c)` is the
Möbius action of `moebiusGL` (`LinearAlgebra/Matrix/GeneralLinearGroup/MoebiusZMod.lean`) at
`γ` reduced modulo `p`, so it is a bijection for free (`descendIndexPerm_bijective`): the affine
index with `a + j c ≡ 0` — which exists exactly when `p ∤ c` — goes to `∞`, and `∞` comes back to
`d / c`.

## The factorisation

Every case is the general upper-triangular factorisation
`HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul_of_isUnit`, applied to `γ` twisted by `γ_p`:
to `γ` itself at an affine index with `a + j c` a unit, to `γ γ_p⁻¹` at the degenerate affine
index, to `γ_p γ` at `∞` when `p ∤ c`, and to `γ_p γ γ_p⁻¹` at `∞` when `p ∣ c`. Since
`γ_p ≡ S = [0, -1; 1, 0] (mod p)` the twists have computable residues, which is what makes the
denominators units and pins the target indices; since `γ_p ≡ 1 (mod N / p)` every witness has
the lower-right entry of `γ` modulo `N / p`, which is what transporting a nebentypus needs.

## Main definitions

* `TauCeti.descendIndexEquiv`: `Fin (descendMatrixCount p N) ≃ OnePoint (ZMod p)` at `p ∥ N`.
* `TauCeti.descendIndexGL`: `moebiusGL` of `γ` modulo `p`, the element whose action is the
  descent's index map.
* `TauCeti.descendIndexPerm`: that action read back on the index set.

## Main results

* `TauCeti.descendIndexPerm_bijective`: the index map is a bijection.
* `TauCeti.exists_mem_Gamma0_descendMatrix_mul_of_not_sq_dvd`: for `p ∥ N` and
  `γ ∈ Γ₀(N / p)`, `descendMatrix p N v * γ = α * descendMatrix p N (descendIndexPerm … v)` for
  some `α ∈ Γ₀(N)` with `α 1 1 ≡ γ 1 1 (mod N / p)`; assembled from the four cases
  `…_of_isUnit`, `…_of_eq_zero`, `…_of_le_of_ne_zero` and `…_of_le_of_eq_zero`.
* `TauCeti.descendExtraGamma_apply_intCast_zmod`: the residues of the extra matrix modulo `p`.

## Scope

Only the `p ∥ N` case; `p² ∣ N` is `exists_mem_Gamma0_descendMatrix_mul` in `Action.lean`, and
a statement uniform in the two cases is not made here. The invariance of the slash sum and the
behaviour at cusps are separate statements and neither is claimed.

Corresponds to `descendCosetList_action_upper_tri_extra`, `descendCosetList_action_extra` and
`descendCosetList_action` (the `p² ∤ N` branch, including its `Gamma0MapUnits` compatibility) of
the AINTLIB `LeanModularForms` project
(`LeanModularForms/StrongMultiplicityOne/DescentCosets.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>). The source
handles the pole by a direct matrix computation and proves bijectivity of the index map by an
injectivity argument on `Fin (p + 1)`; here both come from the projective line.
-/

public section

open CongruenceSubgroup HeckeRing.GL2 Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups OnePoint

namespace TauCeti

variable {p N : ℕ}

/-- **At a prime exactly dividing `N`, the descent's index set is the projective line over
`ZMod p`.** `descendMatrixCount p N` is `p + 1` there, and `Fin (p + 1) ≃ Option (Fin p) ≃
Option (ZMod p)`, which is `OnePoint (ZMod p)`: the upper-triangular members are the affine
points and the extra representative is `∞`. -/
def descendIndexEquiv (p N : ℕ) [NeZero p] (hpsq : ¬ p ^ 2 ∣ N) :
    Fin (descendMatrixCount p N) ≃ OnePoint (ZMod p) :=
  (finCongr (descendMatrixCount_of_not_sq_dvd hpsq)).trans
    (finSuccEquivLast.trans (ZMod.finEquiv p).toEquiv.optionCongr)

/-- An index below `p` is the affine point it names. -/
@[simp] theorem descendIndexEquiv_apply_of_lt [NeZero p] (hpsq : ¬ p ^ 2 ∣ N)
    {v : Fin (descendMatrixCount p N)} (hv : v.val < p) :
    descendIndexEquiv p N hpsq v = (((v : ℕ) : ZMod p) : OnePoint (ZMod p)) := by
  have hcast : Fin.cast (descendMatrixCount_of_not_sq_dvd hpsq) v = Fin.castSucc ⟨v.val, hv⟩ :=
    Fin.ext rfl
  rw [descendIndexEquiv]
  change (ZMod.finEquiv p).toEquiv.optionCongr
    (finSuccEquivLast (Fin.cast (descendMatrixCount_of_not_sq_dvd hpsq) v)) = _
  rw [hcast, finSuccEquivLast_castSucc, Equiv.optionCongr_apply, Option.map_some]
  exact congrArg some (ZMod.finEquiv_apply ⟨v.val, hv⟩)

/-- The index `p` is the point at infinity. -/
@[simp] theorem descendIndexEquiv_apply_of_le [NeZero p] (hpsq : ¬ p ^ 2 ∣ N)
    {v : Fin (descendMatrixCount p N)} (hv : p ≤ v.val) :
    descendIndexEquiv p N hpsq v = ∞ := by
  have hcast : Fin.cast (descendMatrixCount_of_not_sq_dvd hpsq) v = Fin.last p := by
    have hlt := v.isLt
    have hcount := descendMatrixCount_of_not_sq_dvd (p := p) hpsq
    exact Fin.ext (by rw [Fin.val_cast, Fin.val_last]; omega)
  rw [descendIndexEquiv]
  change (ZMod.finEquiv p).toEquiv.optionCongr
    (finSuccEquivLast (Fin.cast (descendMatrixCount_of_not_sq_dvd hpsq) v)) = _
  rw [hcast, finSuccEquivLast_last, Equiv.optionCongr_apply, Option.map_none]
  rfl

/-- The index of an affine point is its representative below `p`. -/
theorem descendIndexEquiv_symm_coe_val [NeZero p] (hpsq : ¬ p ^ 2 ∣ N) (k : ZMod p) :
    ((descendIndexEquiv p N hpsq).symm (k : OnePoint (ZMod p)) : ℕ) = k.val := by
  have hk : k.val < descendMatrixCount p N := by
    rw [descendMatrixCount_of_not_sq_dvd hpsq]
    exact k.val_lt.trans (Nat.lt_succ_self p)
  have : (descendIndexEquiv p N hpsq).symm (k : OnePoint (ZMod p)) = ⟨k.val, hk⟩ := by
    rw [Equiv.symm_apply_eq, descendIndexEquiv_apply_of_lt hpsq (v := ⟨k.val, hk⟩) k.val_lt]
    simp
  rw [this]

/-- The index of the point at infinity is `p`. -/
theorem descendIndexEquiv_symm_infty_val [NeZero p] (hpsq : ¬ p ^ 2 ∣ N) :
    ((descendIndexEquiv p N hpsq).symm ∞ : ℕ) = p := by
  have hp : p < descendMatrixCount p N := by
    rw [descendMatrixCount_of_not_sq_dvd hpsq]
    exact Nat.lt_succ_self p
  have : (descendIndexEquiv p N hpsq).symm ∞ = ⟨p, hp⟩ := by
    rw [Equiv.symm_apply_eq, descendIndexEquiv_apply_of_le hpsq (v := ⟨p, hp⟩) le_rfl]
  rw [this]

/-- **The Möbius element of the descent at `γ`**: `moebiusGL` of `γ` reduced modulo `p`, whose
action on the projective line is the descent's index map `j ↦ (b + j d) / (a + j c)`. -/
noncomputable def descendIndexGL (p : ℕ) [Fact p.Prime] (γ : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  moebiusGL ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod p))) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]
    exact one_ne_zero)

/-- The value of the descent's Möbius element at an affine point, in the entries of `γ`. -/
theorem descendIndexGL_smul_coe [Fact p.Prime] (γ : SL(2, ℤ)) (k : ZMod p) :
    descendIndexGL p γ • (k : OnePoint (ZMod p))
      = if ((γ 1 0 : ℤ) : ZMod p) * k + ((γ 0 0 : ℤ) : ZMod p) = 0 then ∞
        else ((((γ 1 1 : ℤ) : ZMod p) * k + ((γ 0 1 : ℤ) : ZMod p))
          / (((γ 1 0 : ℤ) : ZMod p) * k + ((γ 0 0 : ℤ) : ZMod p)) : ZMod p) := by
  rw [descendIndexGL, moebiusGL_smul_some]
  simp only [Matrix.map_apply, eq_intCast]

/-- The value of the descent's Möbius element at the point at infinity. -/
theorem descendIndexGL_smul_infty [Fact p.Prime] (γ : SL(2, ℤ)) :
    descendIndexGL p γ • (∞ : OnePoint (ZMod p))
      = if ((γ 1 0 : ℤ) : ZMod p) = 0 then ∞
        else (((γ 1 1 : ℤ) : ZMod p) / ((γ 1 0 : ℤ) : ZMod p) : ZMod p) := by
  rw [descendIndexGL, moebiusGL_smul_infty]
  simp only [Matrix.map_apply, eq_intCast]

/-- **An affine index with `a + j c` a unit goes to the offset map's value.** -/
theorem descendIndexGL_smul_coe_of_isUnit [NeZero p] [Fact p.Prime] {γ : SL(2, ℤ)} {j : Fin p}
    (hA : IsUnit (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p))) :
    descendIndexGL p γ • (((j : ℕ) : ZMod p) : OnePoint (ZMod p))
      = (((upperTriShift p γ j : ℕ) : ZMod p) : OnePoint (ZMod p)) := by
  have hA' : IsUnit (((γ 0 0 : ℤ) : ZMod p) + ((j : ℕ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p)) := by
    push_cast at hA
    exact hA
  have hne : ((γ 1 0 : ℤ) : ZMod p) * ((j : ℕ) : ZMod p) + ((γ 0 0 : ℤ) : ZMod p) ≠ 0 := by
    have := hA'.ne_zero
    intro hz
    exact this (by linear_combination hz)
  rw [descendIndexGL_smul_coe]
  split_ifs with hc
  · exact absurd hc hne
  · rw [OnePoint.coe_eq_coe, div_eq_iff hne]
    linear_combination -(mul_upperTriShift_natCast hA')

/-- **The degenerate affine index goes to infinity.** When `a + j c ≡ 0`, the offset map has no
affine target — which is why the index set is the projective line, not `Fin p`. -/
theorem descendIndexGL_smul_coe_of_eq_zero [Fact p.Prime] {γ : SL(2, ℤ)} {j : Fin p}
    (h : (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)) = 0) :
    descendIndexGL p γ • (((j : ℕ) : ZMod p) : OnePoint (ZMod p)) = ∞ := by
  rw [descendIndexGL_smul_coe]
  push_cast at h
  split_ifs with hc
  · rfl
  · exact absurd (by linear_combination h) hc

/-- **Infinity comes back to `d / c` when `p ∤ c`.** -/
theorem descendIndexGL_smul_infty_of_ne_zero [Fact p.Prime] {γ : SL(2, ℤ)}
    (hc : ((γ 1 0 : ℤ) : ZMod p) ≠ 0) :
    descendIndexGL p γ • (∞ : OnePoint (ZMod p))
      = ((((γ 1 1 : ℤ) : ZMod p) / ((γ 1 0 : ℤ) : ZMod p) : ZMod p) : OnePoint (ZMod p)) := by
  rw [descendIndexGL_smul_infty]
  split_ifs with h
  · exact absurd h hc
  · rfl

/-- **Infinity is fixed when `p ∣ c`.** -/
theorem descendIndexGL_smul_infty_of_eq_zero [Fact p.Prime] {γ : SL(2, ℤ)}
    (hc : ((γ 1 0 : ℤ) : ZMod p) = 0) : descendIndexGL p γ • (∞ : OnePoint (ZMod p)) = ∞ := by
  rw [descendIndexGL_smul_infty]
  split_ifs
  rfl

/-- **The index permutation at a prime exactly dividing `N`**: the Möbius action of
`descendIndexGL p γ` on the projective line, read through `descendIndexEquiv`. -/
noncomputable def descendIndexPerm (p N : ℕ) [NeZero p] [Fact p.Prime] (hpsq : ¬ p ^ 2 ∣ N)
    (γ : SL(2, ℤ)) (v : Fin (descendMatrixCount p N)) : Fin (descendMatrixCount p N) :=
  (descendIndexEquiv p N hpsq).symm (descendIndexGL p γ • descendIndexEquiv p N hpsq v)

/-- The defining equation of `descendIndexPerm`, for rewriting across the module boundary. -/
theorem descendIndexPerm_apply [NeZero p] [Fact p.Prime] (hpsq : ¬ p ^ 2 ∣ N) (γ : SL(2, ℤ))
    (v : Fin (descendMatrixCount p N)) : descendIndexPerm p N hpsq γ v
      = (descendIndexEquiv p N hpsq).symm (descendIndexGL p γ • descendIndexEquiv p N hpsq v) :=
  (rfl)

/-- **The index permutation is a bijection**, because a group action is. -/
theorem descendIndexPerm_bijective [NeZero p] [Fact p.Prime] (hpsq : ¬ p ^ 2 ∣ N)
    (γ : SL(2, ℤ)) : Function.Bijective (descendIndexPerm p N hpsq γ) := by
  have h : descendIndexPerm p N hpsq γ = ((descendIndexEquiv p N hpsq).trans
      ((MulAction.toPerm (descendIndexGL p γ)).trans (descendIndexEquiv p N hpsq).symm)) :=
    funext fun v ↦ descendIndexPerm_apply hpsq γ v
  rw [h]
  exact Equiv.bijective _

/-- **The level hypothesis of the factorisation, for any element of `Γ₀(N / p)`.** `N = p (N / p)`
divides `p c` because `N / p ∣ c`. -/
theorem intCast_mul_apply_one_zero_eq_zero_of_mem_Gamma0_div (hpN : p ∣ N) {δ : SL(2, ℤ)}
    (hδ : δ ∈ Gamma0 (N / p)) : (((p : ℤ) * δ 1 0 : ℤ) : ZMod N) = 0 := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
  have hpNp : (N : ℤ) = (p : ℤ) * ((N / p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hpN).symm
  rw [hpNp]
  exact mul_dvd_mul_left _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ))

/-! ## The residues of the extra matrix and of its twists -/

/-- The residues of the extra matrix modulo `p` are those of `S = [0, -1; 1, 0]`. -/
theorem descendExtraGamma_apply_intCast_zmod (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) :
    ((descendExtraGamma p N 0 0 : ℤ) : ZMod p) = 0 ∧
      ((descendExtraGamma p N 0 1 : ℤ) : ZMod p) = -1 ∧
      ((descendExtraGamma p N 1 0 : ℤ) : ZMod p) = 1 ∧
      ((descendExtraGamma p N 1 1 : ℤ) : ZMod p) = 0 := by
  have hS : ∀ i k, ((descendExtraGamma p N i k : ℤ) : ZMod p)
      = ((ModularGroup.S i k : ℤ) : ZMod p) := fun i k ↦ by
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using congrArg (fun M : SL(2, ZMod p) => (M : Matrix (Fin 2) (Fin 2) (ZMod p)) i k)
        (descendExtraGamma_map_intCast_zmod_eq_S hp hpN hpsq)
  exact ⟨by simpa [ModularGroup.coe_S] using hS 0 0, by simpa [ModularGroup.coe_S] using hS 0 1,
    by simpa [ModularGroup.coe_S] using hS 1 0, by simpa [ModularGroup.coe_S] using hS 1 1⟩

/-- `γ δ⁻¹` entrywise, in the shape `Matrix.mul_fin_two` produces. -/
private theorem coe_mul_inv_fin_two (γ δ : SL(2, ℤ)) :
    ((γ * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![γ 0 0 * δ 1 1 + γ 0 1 * -δ 1 0, γ 0 0 * -δ 0 1 + γ 0 1 * δ 0 0;
          γ 1 0 * δ 1 1 + γ 1 1 * -δ 1 0, γ 1 0 * -δ 0 1 + γ 1 1 * δ 0 0] := by
  conv_lhs => rw [coe_mul, coe_inv, adjugate_fin_two,
    Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ), Matrix.mul_fin_two]

/-- `δ γ` entrywise, in the shape `Matrix.mul_fin_two` produces. -/
private theorem coe_mul_fin_two (δ γ : SL(2, ℤ)) :
    ((δ * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![δ 0 0 * γ 0 0 + δ 0 1 * γ 1 0, δ 0 0 * γ 0 1 + δ 0 1 * γ 1 1;
          δ 1 0 * γ 0 0 + δ 1 1 * γ 1 0, δ 1 0 * γ 0 1 + δ 1 1 * γ 1 1] := by
  conv_lhs => rw [coe_mul, Matrix.eta_fin_two (δ : Matrix (Fin 2) (Fin 2) ℤ),
    Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ), Matrix.mul_fin_two]

/-- The residues of `γ γ_p⁻¹` modulo `p`: those of `γ S⁻¹ = [-b, a; -d, c]`. -/
private theorem mul_inv_descendExtraGamma_apply_intCast_zmod (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) (γ : SL(2, ℤ)) :
    (((γ * (descendExtraGamma p N)⁻¹) 0 0 : ℤ) : ZMod p) = -((γ 0 1 : ℤ) : ZMod p) ∧
      (((γ * (descendExtraGamma p N)⁻¹) 0 1 : ℤ) : ZMod p) = ((γ 0 0 : ℤ) : ZMod p) ∧
      (((γ * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) : ZMod p) = -((γ 1 1 : ℤ) : ZMod p) ∧
      (((γ * (descendExtraGamma p N)⁻¹) 1 1 : ℤ) : ZMod p) = ((γ 1 0 : ℤ) : ZMod p) := by
  obtain ⟨h00, h01, h10, h11⟩ := descendExtraGamma_apply_intCast_zmod hp hpN hpsq
  rw [coe_mul_inv_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero]
    push_cast
    rw [h11, h10]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    rw [h01, h00]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    rw [h11, h10]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    rw [h01, h00]
    ring

/-- The residues of `γ_p γ` modulo `p`: those of `S γ = [-c, -d; a, b]`. -/
private theorem descendExtraGamma_mul_apply_intCast_zmod (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) (γ : SL(2, ℤ)) :
    (((descendExtraGamma p N * γ) 0 0 : ℤ) : ZMod p) = -((γ 1 0 : ℤ) : ZMod p) ∧
      (((descendExtraGamma p N * γ) 0 1 : ℤ) : ZMod p) = -((γ 1 1 : ℤ) : ZMod p) ∧
      (((descendExtraGamma p N * γ) 1 0 : ℤ) : ZMod p) = ((γ 0 0 : ℤ) : ZMod p) ∧
      (((descendExtraGamma p N * γ) 1 1 : ℤ) : ZMod p) = ((γ 0 1 : ℤ) : ZMod p) := by
  obtain ⟨h00, h01, h10, h11⟩ := descendExtraGamma_apply_intCast_zmod hp hpN hpsq
  rw [coe_mul_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero]
    push_cast
    rw [h00, h01]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    rw [h00, h01]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    rw [h10, h11]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    rw [h10, h11]
    ring

/-- The residues of `γ_p γ γ_p⁻¹` modulo `p`: those of `S γ S⁻¹ = [d, -c; -b, a]`. -/
private theorem descendExtraGamma_mul_mul_inv_apply_intCast_zmod (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) (γ : SL(2, ℤ)) :
    (((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 0 0 : ℤ) : ZMod p)
        = ((γ 1 1 : ℤ) : ZMod p) ∧
      (((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 0 1 : ℤ) : ZMod p)
        = -((γ 1 0 : ℤ) : ZMod p) := by
  obtain ⟨h00, h01, h10, h11⟩ := descendExtraGamma_apply_intCast_zmod hp hpN hpsq
  obtain ⟨e00, e01, -, -⟩ := descendExtraGamma_mul_apply_intCast_zmod hp hpN hpsq γ
  rw [coe_mul_inv_fin_two]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero]
    push_cast
    rw [e00, e01, h11, h10]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    rw [e00, e01, h01, h00]
    ring

/-- Modulo `N / p` the extra matrix is the identity, so any twist by it has the lower-right entry
of `γ`. Stated for a matrix `δ` whose reduction agrees with that of `γ`. -/
private theorem intCast_apply_one_one_zmod_div_eq_of_map_eq {δ γ : SL(2, ℤ)}
    (h : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (N / p))) δ
      = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (N / p))) γ) :
    ((δ 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) := by
  have := congrArg
    (fun M : SL(2, ZMod (N / p)) => (M : Matrix (Fin 2) (Fin 2) (ZMod (N / p))) 1 1) h
  simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    eq_intCast] using this

/-- The entry equation of the factorisation reads as a congruence at any level where `c`
vanishes. -/
theorem intCast_apply_one_one_eq_of_mem_Gamma0_of_eq {M : ℕ} {δ α : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M)
    {k : ℤ} (h : (α 1 1 : ℤ) = δ 1 1 - δ 1 0 * k) :
    ((α 1 1 : ℤ) : ZMod M) = ((δ 1 1 : ℤ) : ZMod M) := by
  rw [h]
  push_cast
  rw [Gamma0_mem.mp hδ]
  ring

/-! ## The four cases of the factorisation -/

/-- **An affine index with `a + j c` a unit stays affine**, at the offset map's value: the
factorisation is the upper-triangular one, unchanged. -/
theorem exists_mem_Gamma0_descendMatrix_mul_of_isUnit [NeZero p] [Fact p.Prime] (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    {v : Fin (descendMatrixCount p N)} (hv : v.val < p)
    (hA : IsUnit (((γ 0 0 + (v : ℕ) * γ 1 0 : ℤ) : ZMod p))) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧ ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) ∧
      descendMatrix p N v * mapGL ℝ γ
        = mapGL ℝ α * descendMatrix p N (descendIndexPerm p N hpsq γ v) := by
  obtain ⟨α, hα, hd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_isUnit (j := ⟨v.val, hv⟩) hA
    (intCast_mul_apply_one_zero_eq_zero_of_mem_Gamma0_div hpN hγ)
  have hidx : (descendIndexPerm p N hpsq γ v : ℕ) = (upperTriShift p γ ⟨v.val, hv⟩ : ℕ) := by
    rw [descendIndexPerm_apply, descendIndexEquiv_apply_of_lt hpsq hv,
      descendIndexGL_smul_coe_of_isUnit (j := ⟨v.val, hv⟩) hA, descendIndexEquiv_symm_coe_val,
      ZMod.val_natCast_of_lt (upperTriShift p γ ⟨v.val, hv⟩).isLt]
  have hv' : (descendIndexPerm p N hpsq γ v : ℕ) < p :=
    hidx ▸ (upperTriShift p γ ⟨v.val, hv⟩).isLt
  have htgt : (⟨(descendIndexPerm p N hpsq γ v : ℕ), hv'⟩ : Fin p)
      = upperTriShift p γ ⟨v.val, hv⟩ := Fin.ext hidx
  refine ⟨α, hα, intCast_apply_one_one_eq_of_mem_Gamma0_of_eq hγ hd, ?_⟩
  simpa only [descendMatrix_of_lt hv, descendMatrix_of_lt hv', htgt, map_mul, map_mapGL]
    using congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hmul

/-- At the degenerate affine index the twist `γ γ_p⁻¹ ≡ γ S⁻¹` has unit denominator
`-(b + j d)` — both `a + j c` and `b + j d` cannot vanish, by `a d - b c = 1` — and its offset map
sends `j` to `0`. -/
private theorem mul_inv_descendExtraGamma_isUnit_and_upperTriShift_eq [NeZero p] [Fact p.Prime]
    (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} {j : Fin p}
    (h0 : (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)) = 0) :
    IsUnit ((((γ * (descendExtraGamma p N)⁻¹) 0 0
        + (j : ℕ) * (γ * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) : ZMod p)) ∧
      upperTriShift p (γ * (descendExtraGamma p N)⁻¹) j = ⟨0, NeZero.pos p⟩ := by
  have hp : p.Prime := Fact.out
  obtain ⟨hδ00, hδ01, hδ10, hδ11⟩ := mul_inv_descendExtraGamma_apply_intCast_zmod hp hpN hpsq γ
  have hdet : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod p) = 1 := by
    rw [Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ, Int.cast_one]
  have hA' : IsUnit ((((γ * (descendExtraGamma p N)⁻¹) 0 0 : ℤ) : ZMod p)
      + ((j : ℕ) : ZMod p) * (((γ * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) : ZMod p)) := by
    rw [hδ00, hδ10]
    refine isUnit_iff_ne_zero.mpr fun hz ↦ one_ne_zero (α := ZMod p) ?_
    push_cast at h0 hdet
    linear_combination -hdet + ((γ 1 1 : ℤ) : ZMod p) * h0 + ((γ 1 0 : ℤ) : ZMod p) * hz
  refine ⟨by push_cast; exact hA', ?_⟩
  rw [upperTriShift_eq_iff hA', hδ01, hδ11]
  simp only [Nat.cast_zero, mul_zero]
  push_cast at h0
  exact h0.symm

/-- At `∞` with `p ∤ c` the twist `γ_p γ ≡ S γ` has unit denominator `-c` at `0`, and its offset
map sends `0` to `d / c`. -/
private theorem descendExtraGamma_mul_isUnit_and_upperTriShift_eq [NeZero p] [Fact p.Prime]
    (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hc : ((γ 1 0 : ℤ) : ZMod p) ≠ 0) :
    IsUnit ((((descendExtraGamma p N * γ) 0 0
        + ((⟨0, NeZero.pos p⟩ : Fin p) : ℕ) * (descendExtraGamma p N * γ) 1 0 : ℤ) : ZMod p)) ∧
      ((upperTriShift p (descendExtraGamma p N * γ) ⟨0, NeZero.pos p⟩ : ℕ) : ZMod p)
        = ((γ 1 1 : ℤ) : ZMod p) / ((γ 1 0 : ℤ) : ZMod p) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hδ00, hδ01, -, -⟩ := descendExtraGamma_mul_apply_intCast_zmod hp hpN hpsq γ
  have hA' : IsUnit ((((descendExtraGamma p N * γ) 0 0 : ℤ) : ZMod p)
      + (((⟨0, NeZero.pos p⟩ : Fin p) : ℕ) : ZMod p)
        * (((descendExtraGamma p N * γ) 1 0 : ℤ) : ZMod p)) := by
    simp only [Nat.cast_zero, zero_mul, add_zero, hδ00]
    exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hc)
  refine ⟨by push_cast; simpa only [Nat.cast_zero, zero_mul, add_zero] using hA', ?_⟩
  have h := mul_upperTriShift_natCast hA'
  simp only [Nat.cast_zero, zero_mul, add_zero, hδ00, hδ01] at h
  rw [eq_div_iff hc]
  linear_combination -h

/-- At `∞` with `p ∣ c` the twist `γ_p γ γ_p⁻¹ ≡ S γ S⁻¹` has unit denominator `d` at `0` — as
`a d ≡ 1` — and its offset map sends `0` to `-c / d ≡ 0`. -/
private theorem descendExtraGamma_mul_mul_inv_isUnit_and_upperTriShift_eq [NeZero p]
    [Fact p.Prime] (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)}
    (hc : ((γ 1 0 : ℤ) : ZMod p) = 0) :
    IsUnit ((((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 0 0
        + ((⟨0, NeZero.pos p⟩ : Fin p) : ℕ)
          * (descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) : ZMod p)) ∧
      upperTriShift p (descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) ⟨0, NeZero.pos p⟩
        = ⟨0, NeZero.pos p⟩ := by
  have hp : p.Prime := Fact.out
  obtain ⟨hδ00, hδ01⟩ := descendExtraGamma_mul_mul_inv_apply_intCast_zmod hp hpN hpsq γ
  have hdet : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod p) = 1 := by
    rw [Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ, Int.cast_one]
  have hA' : IsUnit ((((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 0 0 : ℤ) : ZMod p)
      + (((⟨0, NeZero.pos p⟩ : Fin p) : ℕ) : ZMod p)
        * (((descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) : ZMod p)) := by
    simp only [Nat.cast_zero, zero_mul, add_zero, hδ00]
    refine isUnit_iff_ne_zero.mpr fun hz ↦ one_ne_zero (α := ZMod p) ?_
    push_cast at hdet
    linear_combination -hdet + ((γ 0 0 : ℤ) : ZMod p) * hz - ((γ 0 1 : ℤ) : ZMod p) * hc
  refine ⟨by push_cast; simpa only [Nat.cast_zero, zero_mul, add_zero] using hA', ?_⟩
  rw [upperTriShift_eq_iff hA', hδ01, hc]
  simp only [Nat.cast_zero, mul_zero, zero_mul, neg_zero, add_zero]

/-- **The degenerate affine index goes to the extra representative.** The factorisation of the
twist `γ γ_p⁻¹` at `j` lands on `[1, 0; 0, p]`; multiplying it back by `γ_p` lands on the extra
member `[1, 0; 0, p] γ_p`. -/
theorem exists_mem_Gamma0_descendMatrix_mul_of_eq_zero [NeZero p] [Fact p.Prime] (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    {v : Fin (descendMatrixCount p N)} (hv : v.val < p)
    (h0 : (((γ 0 0 + (v : ℕ) * γ 1 0 : ℤ) : ZMod p)) = 0) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧ ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) ∧
      descendMatrix p N v * mapGL ℝ γ
        = mapGL ℝ α * descendMatrix p N (descendIndexPerm p N hpsq γ v) := by
  have hp : p.Prime := Fact.out
  have hδ : γ * (descendExtraGamma p N)⁻¹ ∈ Gamma0 (N / p) :=
    Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ (descendExtraGamma_mem_Gamma0 hp hpN hpsq))
  obtain ⟨hA, hshift⟩ :=
    mul_inv_descendExtraGamma_isUnit_and_upperTriShift_eq (j := ⟨v.val, hv⟩) hpN hpsq h0
  obtain ⟨α, hα, hd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_isUnit hA
    (intCast_mul_apply_one_zero_eq_zero_of_mem_Gamma0_div hpN hδ)
  have hidx : (descendIndexPerm p N hpsq γ v : ℕ) = p := by
    rw [descendIndexPerm_apply, descendIndexEquiv_apply_of_lt hpsq hv,
      descendIndexGL_smul_coe_of_eq_zero (j := ⟨v.val, hv⟩) h0, descendIndexEquiv_symm_infty_val]
  refine ⟨α, hα, (intCast_apply_one_one_eq_of_mem_Gamma0_of_eq hδ hd).trans ?_, ?_⟩
  · refine intCast_apply_one_one_zmod_div_eq_of_map_eq ?_
    rw [map_mul, map_inv, descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq, inv_one,
      mul_one]
  · have h := congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hmul
    simp only [map_mul, map_mapGL, hshift] at h
    rw [descendMatrix_of_lt hv, descendMatrix_of_le hidx.ge,
      ← inv_mul_cancel_right γ (descendExtraGamma p N), map_mul, map_mul, ← mul_assoc, h,
      mul_assoc]

/-- **The extra representative moves into the affine line when `p ∤ c`**, landing at `d / c`:
the factorisation of the twist `γ_p γ` at `0`. -/
theorem exists_mem_Gamma0_descendMatrix_mul_of_le_of_ne_zero [NeZero p] [Fact p.Prime]
    (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    {v : Fin (descendMatrixCount p N)} (hv : p ≤ v.val) (hc : ((γ 1 0 : ℤ) : ZMod p) ≠ 0) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧ ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) ∧
      descendMatrix p N v * mapGL ℝ γ
        = mapGL ℝ α * descendMatrix p N (descendIndexPerm p N hpsq γ v) := by
  have hp : p.Prime := Fact.out
  have hδ : descendExtraGamma p N * γ ∈ Gamma0 (N / p) :=
    Subgroup.mul_mem _ (descendExtraGamma_mem_Gamma0 hp hpN hpsq) hγ
  obtain ⟨hA, hshift⟩ := descendExtraGamma_mul_isUnit_and_upperTriShift_eq hpN hpsq hc
  obtain ⟨α, hα, hd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_isUnit hA
    (intCast_mul_apply_one_zero_eq_zero_of_mem_Gamma0_div hpN hδ)
  have hidx : (descendIndexPerm p N hpsq γ v : ℕ)
      = (upperTriShift p (descendExtraGamma p N * γ) ⟨0, NeZero.pos p⟩ : ℕ) := by
    rw [descendIndexPerm_apply, descendIndexEquiv_apply_of_le hpsq hv,
      descendIndexGL_smul_infty_of_ne_zero hc, descendIndexEquiv_symm_coe_val, ← hshift,
      ZMod.val_natCast_of_lt (upperTriShift p (descendExtraGamma p N * γ) ⟨0, NeZero.pos p⟩).isLt]
  have hv' : (descendIndexPerm p N hpsq γ v : ℕ) < p :=
    hidx ▸ (upperTriShift p (descendExtraGamma p N * γ) ⟨0, NeZero.pos p⟩).isLt
  have htgt : (⟨(descendIndexPerm p N hpsq γ v : ℕ), hv'⟩ : Fin p)
      = upperTriShift p (descendExtraGamma p N * γ) ⟨0, NeZero.pos p⟩ := Fin.ext hidx
  refine ⟨α, hα, (intCast_apply_one_one_eq_of_mem_Gamma0_of_eq hδ hd).trans ?_, ?_⟩
  · refine intCast_apply_one_one_zmod_div_eq_of_map_eq ?_
    rw [map_mul, descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq, one_mul]
  · rw [descendMatrix_of_le hv, descendMatrix_of_lt hv', htgt, mul_assoc, ← map_mul]
    simpa only [map_mul, map_mapGL]
      using congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hmul

/-- **The extra representative is fixed when `p ∣ c`**: the factorisation of the twist
`γ_p γ γ_p⁻¹` at `0` lands on `[1, 0; 0, p]`, and multiplying back by `γ_p` returns to the extra
member. -/
theorem exists_mem_Gamma0_descendMatrix_mul_of_le_of_eq_zero [NeZero p] [Fact p.Prime]
    (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    {v : Fin (descendMatrixCount p N)} (hv : p ≤ v.val) (hc : ((γ 1 0 : ℤ) : ZMod p) = 0) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧ ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) ∧
      descendMatrix p N v * mapGL ℝ γ
        = mapGL ℝ α * descendMatrix p N (descendIndexPerm p N hpsq γ v) := by
  have hp : p.Prime := Fact.out
  have hγp : descendExtraGamma p N ∈ Gamma0 (N / p) := descendExtraGamma_mem_Gamma0 hp hpN hpsq
  have hδ : descendExtraGamma p N * γ * (descendExtraGamma p N)⁻¹ ∈ Gamma0 (N / p) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hγp hγ) (Subgroup.inv_mem _ hγp)
  obtain ⟨hA, hshift⟩ := descendExtraGamma_mul_mul_inv_isUnit_and_upperTriShift_eq hpN hpsq hc
  obtain ⟨α, hα, hd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_isUnit hA
    (intCast_mul_apply_one_zero_eq_zero_of_mem_Gamma0_div hpN hδ)
  have hidx : (descendIndexPerm p N hpsq γ v : ℕ) = p := by
    rw [descendIndexPerm_apply, descendIndexEquiv_apply_of_le hpsq hv,
      descendIndexGL_smul_infty_of_eq_zero hc, descendIndexEquiv_symm_infty_val]
  refine ⟨α, hα, (intCast_apply_one_one_eq_of_mem_Gamma0_of_eq hδ hd).trans ?_, ?_⟩
  · refine intCast_apply_one_one_zmod_div_eq_of_map_eq ?_
    rw [map_mul, map_mul, map_inv, descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq,
      inv_one, one_mul, mul_one]
  · have h := congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hmul
    simp only [map_mul, map_mapGL, hshift] at h
    rw [descendMatrix_of_le hv, descendMatrix_of_le hidx.ge, mul_assoc, ← map_mul,
      ← inv_mul_cancel_right (descendExtraGamma p N * γ) (descendExtraGamma p N), map_mul,
      map_mul, map_mul, ← mul_assoc, h, mul_assoc]

/-- **The descent family is permuted by `Γ₀(N / p)` when `p` exactly divides `N`.** For
`γ ∈ Γ₀(N / p)`, the product `descendMatrix p N v * γ` is an element of `Γ₀(N)` times the member
of the family at `descendIndexPerm p N hpsq γ v`, a bijection of the index set by
`descendIndexPerm_bijective`; and the `Γ₀(N)` witness has the lower-right entry of `γ` modulo
`N / p`. -/
theorem exists_mem_Gamma0_descendMatrix_mul_of_not_sq_dvd [NeZero p] [Fact p.Prime] (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    (v : Fin (descendMatrixCount p N)) :
    ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧ ((α 1 1 : ℤ) : ZMod (N / p)) = ((γ 1 1 : ℤ) : ZMod (N / p)) ∧
      descendMatrix p N v * mapGL ℝ γ
        = mapGL ℝ α * descendMatrix p N (descendIndexPerm p N hpsq γ v) := by
  rcases lt_or_ge v.val p with hv | hv
  · by_cases h0 : (((γ 0 0 + (v : ℕ) * γ 1 0 : ℤ) : ZMod p)) = 0
    · exact exists_mem_Gamma0_descendMatrix_mul_of_eq_zero hpN hpsq hγ hv h0
    · exact exists_mem_Gamma0_descendMatrix_mul_of_isUnit hpN hpsq hγ hv
        (isUnit_iff_ne_zero.mpr h0)
  · by_cases hc : ((γ 1 0 : ℤ) : ZMod p) = 0
    · exact exists_mem_Gamma0_descendMatrix_mul_of_le_of_eq_zero hpN hpsq hγ hv hc
    · exact exists_mem_Gamma0_descendMatrix_mul_of_le_of_ne_zero hpN hpsq hγ hv hc

end TauCeti
