/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.ModularForms.CuspDescent

/-!
# The level-lowering dichotomy

`CuspDescent.lean` builds the descent half of the conductor theorem: when the nebentypus `χ` is
trivial on the kernel of `(ZMod N)ˣ → (ZMod (N / l))ˣ`, the function `f` whose level-raise is a
cusp form of level `N` is itself a cusp form of level `N / l`. That is one horn of a dichotomy.
This file supplies the other horn — when `χ` is *not* trivial on that kernel, `f` vanishes — and
then puts the two together.

## The shape of the vanishing argument

The obstruction is read off a single unit. If `χ` is nontrivial on the kernel, pick `u` in the
kernel with `χ u ≠ 1`, and lift it to `Γ₀(N)`. Slashing `f` by the `diag(l, 1)`-conjugate of that
lift multiplies `f` by `χ u`. But the same conjugate can be *refactored*: `u` may be replaced by
any `u'` in its `ZMod.unitsMap`-coset at the cost of two translations `T ^ i` and `T ^ j`, and `f`
is `T`-periodic, so the translations contribute nothing. Choosing `u'` with `χ u' ≠ χ u` — which
is exactly what nontriviality on the kernel provides — exhibits `f ∣[k] A` as both `χ u • f` and
`χ u' • f` for one matrix `A`. Two distinct multipliers for one slash force `f = 0`.

The refactoring step needs the lift's lower-left entry to be *exactly* `N`, not merely divisible
by it, because `conjScale l · c` records the cofactor `c` and the argument compares the cofactors
of two lifts. That is what `TauCeti.gamma0LiftOfUnit` is for: an explicit Bézout lift
`!![a, b; N, e]` of a prescribed unit, with `a` and `e` the values of `u⁻¹` and `u`.

## Main results

* `TauCeti.gamma0LiftOfUnit`: the controlled `Γ₀(N)` lift of a unit, with lower-left entry `N`,
  together with its four entries and the fact that it lifts the unit it was built from.
* `TauCeti.exists_unitsMap_eq_and_apply_ne`: character separation along a `ZMod.unitsMap`-coset.
* `TauCeti.eq_zero_of_not_forall_unitsMap_eq_one`: **the vanishing horn**.
* `TauCeti.cuspFormOfSmulSlashScaleGL_mem_cuspFormCharSpace`: the descent horn carries the
  lowered nebentypus `hfac.χ₀`.
* `TauCeti.exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero`: **the level-lowering dichotomy**, in
  the roadmap's `DirichletCharacter` phrasing — either `χ` factors through `N / l` and `f` is a
  cusp form of level `N / l` for the lowered character, or `f = 0`.

## Implementation notes

`CuspDescent.lean` carries its character as the units homomorphism `(ZMod N)ˣ →* ℂˣ` that
`cuspFormCharSpace` is indexed by, with the descent hypothesis `∀ u, ZMod.unitsMap _ u = 1 →
χ u = 1`. The vanishing horn below is stated over the *same* homomorphism with the *negation* of
that hypothesis, so the dichotomy is a `by_cases` on one proposition and neither horn has to
restate the other's hypotheses. Only the final theorem is phrased over a `DirichletCharacter`,
where `FactorsThrough` and the lowered character `FactorsThrough.χ₀` live; the bridge between the
two phrasings is mathlib's `DirichletCharacter.factorsThrough_iff_ker_unitsMap`.

## References

* [Miyake, *Modular forms*][miyake1989], Theorem 4.6.4.
* Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Chris Birkbeck, Apache-2.0) at
  commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
  `projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean` lines 542-887 —
  the Case B block of `conductor_theorem_dichotomy_cuspForm_strong`. The source's
  `levelRaiseConjOfDvd` is this repository's `conjScale`, its `levelRaiseFun l k f` is
  `l ^ (1 - k) • (f ∣[k] scaleGL l)`, and its `Gamma0MapUnits` is `(Gamma0Map N).toHomUnits`, so
  none of those three is ported again. The source's `exists_T_levelRaiseConj_T_factor` is already
  here as `exists_eq_T_zpow_mul_conjScale_mul_T_zpow`, and its `loweredCharacter` is mathlib's
  `DirichletCharacter.FactorsThrough.χ₀`.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

/-! ### Character separation along a coset -/

variable {N : ℕ} [NeZero N] {d : ℕ}

omit [NeZero N] in
/-- If a character of `(ZMod N)ˣ` is not trivial on the kernel of `ZMod.unitsMap`, then every
unit has a partner in its `ZMod.unitsMap`-coset on which the character takes a different value.
This is the only consequence of nontriviality the vanishing argument uses. -/
theorem exists_unitsMap_eq_and_apply_ne (hd : d ∣ N) {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : ¬ ∀ u : (ZMod N)ˣ, ZMod.unitsMap hd u = 1 → χ u = 1) (u : (ZMod N)ˣ) : ∃ u' :
    (ZMod N)ˣ, ZMod.unitsMap hd u' = ZMod.unitsMap hd u ∧ χ u' ≠ χ u := by
  -- the failure of triviality is a single kernel unit `v` with `χ v ≠ 1`; translating `u` by it
  -- stays in the coset and moves the value, since `χ (u * v) = χ u * χ v`
  obtain ⟨v, hv, hχv⟩ : ∃ v : (ZMod N)ˣ, ZMod.unitsMap hd v = 1 ∧ χ v ≠ 1 := by
    simpa only [not_forall, exists_prop] using hχ
  exact ⟨u * v, by rw [map_mul, hv, mul_one], fun h ↦ hχv <| mul_left_cancel <| by
    rw [← map_mul, h, mul_one]⟩

/-! ### The controlled `Γ₀(N)` lift of a unit -/

/-- `N` divides `(u⁻¹).val * u.val - 1`, the determinant defect of the Bézout lift below. -/
private lemma N_dvd_unit_val_mul_val_sub_one (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) : (N : ℤ) ∣
    ((((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) * (((u : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id, ← Units.val_mul,
    inv_mul_cancel, Units.val_one]
  ring

/-- **The controlled `Γ₀(N)` lift of a unit.** The Bézout matrix `!![a, b; N, e]` with
`e = (u : ZMod N).val`, `a = (u⁻¹ : ZMod N).val` and `b = (a * e - 1) / N`. Its lower-left entry
is `N` on the nose — that is the point of the construction, since the refactoring step compares
the cofactors of two such lifts — and its lower-right entry is a representative of `u`. -/
noncomputable def gamma0LiftOfUnit (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) : ↥(Gamma0 N) := by
  have hdet : (!![((u⁻¹ : (ZMod N)ˣ) : ZMod N).val, ((((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) *
      (((u : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) / (N : ℤ);
      (N : ℤ), ((u : (ZMod N)ˣ) : ZMod N).val] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linarith [Int.ediv_mul_cancel (N_dvd_unit_val_mul_val_sub_one N u)]
  -- keep the matrix at type `SL(2, ℤ)`: `SpecialLinearGroup` is a semireducible `def` over a
  -- subtype, so an anonymous constructor at the expected type does not unify with `Gamma0_mem`
  set γ : SL(2, ℤ) := ⟨_, hdet⟩ with hγ
  refine ⟨γ, ?_⟩
  rw [Gamma0_mem]
  simp [hγ]

/-- The lower-left entry of the controlled lift is `N` on the nose. -/
@[simp]
lemma gamma0LiftOfUnit_apply_one_zero (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (gamma0LiftOfUnit N u : SL(2, ℤ)) 1 0 = (N : ℤ) := by
  rw [gamma0LiftOfUnit]
  simp

/-- The lower-right entry of the controlled lift is the value of `u`. -/
@[simp]
lemma gamma0LiftOfUnit_apply_one_one (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (gamma0LiftOfUnit N u : SL(2, ℤ)) 1 1 = (((u : (ZMod N)ˣ) : ZMod N).val : ℤ) := by
  rw [gamma0LiftOfUnit]
  simp

/-- The upper-left entry of the controlled lift is the value of `u⁻¹`. -/
@[simp]
lemma gamma0LiftOfUnit_apply_zero_zero (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (gamma0LiftOfUnit N u : SL(2, ℤ)) 0 0 = (((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) := by
  rw [gamma0LiftOfUnit]
  simp

/-- The upper-right entry of the controlled lift is the Bézout cofactor. -/
@[simp]
lemma gamma0LiftOfUnit_apply_zero_one (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (gamma0LiftOfUnit N u : SL(2, ℤ)) 0 1 =
    ((((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) * (((u : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) /
    (N : ℤ) := by
  rw [gamma0LiftOfUnit]
  simp

/-- **The controlled lift lifts the unit it was built from.** This is what makes the lift usable:
the nebentypus reads the lower-right entry, and here that entry is a representative of `u`. -/
@[simp]
lemma Gamma0Map_toHomUnits_gamma0LiftOfUnit (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (Gamma0Map N).toHomUnits (gamma0LiftOfUnit N u) = u := by
  refine Units.ext ?_
  rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply, gamma0LiftOfUnit_apply_one_one]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]


/-- **Units in one `ZMod.unitsMap`-coset have congruent values.** Passing to representatives, two
units with the same image modulo `d` differ by a multiple of `d` in `ℤ`. This is what turns the
character-separating partner into the integer shifts of the refactoring. -/
lemma natCast_dvd_val_sub_val_of_unitsMap_eq (hd : d ∣ N) {u u' : (ZMod N)ˣ}
    (h : ZMod.unitsMap hd u = ZMod.unitsMap hd u') : (d : ℤ) ∣
    ((((u : (ZMod N)ˣ) : ZMod N).val : ℤ) - (((u' : (ZMod N)ˣ) : ZMod N).val : ℤ)) := by
  have hcast : ZMod.castHom hd (ZMod d) ((u : (ZMod N)ˣ) : ZMod N) =
      ZMod.castHom hd (ZMod d) ((u' : (ZMod N)ˣ) : ZMod N) := by
    have hh := congrArg Units.val h
    rwa [ZMod.unitsMap_val, ZMod.unitsMap_val] at hh
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.natCast_val,
    show (ZMod.cast ((u : (ZMod N)ˣ) : ZMod N) : ZMod d) =
      ZMod.castHom hd (ZMod d) ((u : (ZMod N)ˣ) : ZMod N) from
        (ZMod.castHom_apply _).symm,
    show (ZMod.cast ((u' : (ZMod N)ˣ) : ZMod N) : ZMod d) =
      ZMod.castHom hd (ZMod d) ((u' : (ZMod N)ˣ) : ZMod N) from
        (ZMod.castHom_apply _).symm, hcast]
  ring

/-- The lower-left entry of the controlled lift, factored as `l * (N / l)`. This is the shape
`TauCeti.conjScale` asks for, and it records `N / l` as the cofactor. -/
private lemma gamma0LiftOfUnit_apply_one_zero_eq_mul {l : ℕ} (hlN : l ∣ N) (u : (ZMod N)ˣ) :
    (gamma0LiftOfUnit N u : SL(2, ℤ)) 1 0 = (l : ℤ) * ((N / l : ℕ) : ℤ) := by
  rw [gamma0LiftOfUnit_apply_one_zero]
  exact_mod_cast (Nat.mul_div_cancel' hlN).symm


/-! ### Refactoring the conjugated lift through a separating unit -/

/-- The matrix identity behind the refactoring: two Bézout lifts whose upper-left and lower-right
entries agree modulo the cofactor `Nl` differ by translations on both sides. The determinant
hypotheses are what pin the upper-right entries once the other three agree. -/
private lemma eq_T_mul_mul_T_of_sub_eq {l Nl i j a a' e e' b b' : ℤ} (hNl : Nl ≠ 0)
    (hi : i * Nl = a - a') (hj : j * Nl = e - e') (hdet : a * e - b * (l * Nl) = 1)
    (hdet' : a' * e' - b' * (l * Nl) = 1) : (!![a, l * b; Nl, e] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(1 : ℤ), i; 0, 1] * !![a', l * b'; Nl, e'] * !![(1 : ℤ), j; 0, 1] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one,
      cons_val_fin_one, cons_val_zero, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
      head_cons, one_smul, tail_cons, smul_cons, Int.zsmul_eq_mul, smul_empty, empty_vecMul,
      add_zero, add_cons, empty_add_empty, zero_smul, zero_add, empty_mul,
      Equiv.symm_apply_apply, mul_one, mul_zero]
  · linarith
  -- the upper-right entry is the only one the determinants are needed for: both sides agree
  -- after multiplying by the nonzero cofactor `Nl`, so cancel it
  · apply mul_left_cancel₀ hNl
    linear_combination -hdet + hdet' + (-e' - Nl * j) * hi + (-a) * hj
  · linarith

/-- **The refactoring step.** For a character not trivial on the kernel, the `diag(l, 1)`-conjugate
of the controlled lift of `u` is a translate — on both sides — of the conjugate of the controlled
lift of some `u'` on which the character takes a *different* value. Since the function the
vanishing argument is applied to is `T`-periodic, the two translations cost nothing, and the two
sides therefore exhibit one slash with two different multipliers. -/
private theorem exists_eq_T_zpow_mul_conjScale_mul_T_zpow_of_apply_ne {l : ℕ} [NeZero l]
    (hlN : l ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : ¬ ∀ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hlN) u = 1 → χ u = 1) (u : (ZMod N)ˣ)
    : ∃ (i j : ℤ) (u' : (ZMod N)ˣ), χ u' ≠ χ u ∧ conjScale l (gamma0LiftOfUnit N u)
    ((N / l : ℕ) : ℤ)
    (gamma0LiftOfUnit_apply_one_zero_eq_mul hlN u) = ModularGroup.T ^ i * conjScale l
    (gamma0LiftOfUnit N u') ((N / l : ℕ) : ℤ)
    (gamma0LiftOfUnit_apply_one_zero_eq_mul hlN u') * ModularGroup.T ^ j := by
  obtain ⟨u', hcoset, hne⟩ := exists_unitsMap_eq_and_apply_ne (Nat.div_dvd_of_dvd hlN) hχ u
  set a : ℤ := (((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) with ha
  set e : ℤ := (((u : (ZMod N)ˣ) : ZMod N).val : ℤ) with he
  set a' : ℤ := (((u'⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) with ha'
  set e' : ℤ := (((u' : (ZMod N)ˣ) : ZMod N).val : ℤ) with he'
  set Nl : ℤ := ((N / l : ℕ) : ℤ) with hNl
  have hNl_ne : Nl ≠ 0 := by
    rw [hNl, Nat.cast_ne_zero]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hlN) (Nat.pos_of_neZero l)).ne'
  have hNeq : (N : ℤ) = (l : ℤ) * Nl := by
    rw [hNl]; exact_mod_cast (Nat.mul_div_cancel' hlN).symm
  -- the two shifts are the cofactors of the coset congruences, on the inverses and on the units
  have hdvd_a : Nl ∣ (a - a') :=
    natCast_dvd_val_sub_val_of_unitsMap_eq (Nat.div_dvd_of_dvd hlN) (u := u⁻¹) (u' := u'⁻¹)
      (by rw [map_inv, map_inv, hcoset])
  have hdvd_e : Nl ∣ (e - e') :=
    natCast_dvd_val_sub_val_of_unitsMap_eq (Nat.div_dvd_of_dvd hlN) hcoset.symm
  refine ⟨(a - a') / Nl, (e - e') / Nl, u', hne, ?_⟩
  have hdet : a * e - ((a * e - 1) / (N : ℤ)) * ((l : ℤ) * Nl) = 1 := by
    rw [← hNeq]
    linarith [Int.ediv_mul_cancel (N_dvd_unit_val_mul_val_sub_one N u)]
  have hdet' : a' * e' - ((a' * e' - 1) / (N : ℤ)) * ((l : ℤ) * Nl) = 1 := by
    rw [← hNeq]
    linarith [Int.ediv_mul_cancel (N_dvd_unit_val_mul_val_sub_one N u')]
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow, coe_conjScale, coe_conjScale]
  simp only [gamma0LiftOfUnit_apply_zero_zero, gamma0LiftOfUnit_apply_zero_one,
    gamma0LiftOfUnit_apply_one_one, ← ha, ← he, ← ha', ← he', ← hNl]
  exact eq_T_mul_mul_T_of_sub_eq hNl_ne (Int.ediv_mul_cancel hdvd_a)
    (Int.ediv_mul_cancel hdvd_e) hdet hdet'


/-! ### The vanishing horn -/

/-- One slash with two different multipliers forces the function to vanish. -/
lemma eq_zero_of_slash_eq_smul_of_slash_eq_smul (k : ℤ) (f : ℍ → ℂ) (A : GL (Fin 2) ℝ) {z₁ z₂ : ℂ}
    (hne : z₁ ≠ z₂) (h₁ : f ∣[k] A = z₁ • f) (h₂ : f ∣[k] A = z₂ • f) : f = 0 := by
  have hsub : (z₁ - z₂) • f = 0 := by rw [sub_smul, ← h₁, ← h₂, sub_self]
  exact (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)

/-- **The vanishing horn of the level-lowering dichotomy.** If the nebentypus `χ` of the
level-raise of `f` is *not* trivial on the kernel of `(ZMod N)ˣ → (ZMod (N / l))ˣ`, and `f` is
`T`-periodic, then `f = 0`.

The hypotheses `hnb` and `hT` are exactly the ones
`TauCeti.slash_mapGL_eq_self_of_mem_Gamma1_div` takes for the descent, and `hχ` is the negation
of the triviality that `TauCeti.cuspFormOfSmulSlashScaleGL` assumes, so this is the complementary
case of the descent and neither statement restates the other's hypotheses. -/
theorem eq_zero_of_not_forall_unitsMap_eq_one {l : ℕ} [NeZero l] (hlN : l ∣ N) (k : ℤ)
    {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : ¬ ∀ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hlN) u = 1 → χ u = 1) (f : ℍ → ℂ)
    (hnb : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N), (f ∣[k] scaleGL l) ∣[k] mapGL ℝ γ = (χ ((Gamma0Map
      N).toHomUnits ⟨γ, hγ⟩) : ℂ) • (f ∣[k] scaleGL l))
    (hT : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) : f = 0 := by
  -- start from the identity unit; the separation supplies the partner that breaks the tie
  obtain ⟨i, j, u', hne, hfactor⟩ :=
    exists_eq_T_zpow_mul_conjScale_mul_T_zpow_of_apply_ne hlN hχ 1
  have hdet := det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨ModularGroup.T, rfl⟩)
  -- the multiplier attached to the lift of a unit is the character at that unit
  have hmul : ∀ v : (ZMod N)ˣ,
      f ∣[k] (mapGL ℝ (conjScale l (gamma0LiftOfUnit N v) ((N / l : ℕ) : ℤ)
        (gamma0LiftOfUnit_apply_one_zero_eq_mul hlN v)) : GL (Fin 2) ℝ) = (χ v : ℂ) • f := by
    intro v
    have h := slash_conjScale_eq_smul_of_slash_scaleGL (k := k) f (gamma0LiftOfUnit N v)
      (gamma0LiftOfUnit_apply_one_zero_eq_mul hlN v) (hnb _ (gamma0LiftOfUnit N v).property)
    rwa [Subtype.coe_eta, Gamma0Map_toHomUnits_gamma0LiftOfUnit] at h
  -- the same slash, read through the refactoring, has the multiplier of the separating unit
  have halt : f ∣[k] (mapGL ℝ (conjScale l (gamma0LiftOfUnit N 1) ((N / l : ℕ) : ℤ)
      (gamma0LiftOfUnit_apply_one_zero_eq_mul hlN 1)) : GL (Fin 2) ℝ) = (χ u' : ℂ) • f := by
    rw [hfactor, map_mul, map_mul, map_zpow, map_zpow]
    exact slash_zpow_mul_mul_zpow_eq_smul k f hdet hT (hmul u') i j
  exact eq_zero_of_slash_eq_smul_of_slash_eq_smul k f _
    (fun h ↦ hne (Units.ext h)) halt (hmul 1)


/-! ### The dichotomy -/

omit [NeZero N] in
/-- The `T`-factorisation lift carries the same nebentypus label as the element it lifts, once
reduced to level `N / l`. The lower-left entry of a `Γ₀(N / l)` element vanishes there, so the
recorded shift `γ' 1 0 * j` drops out. -/
private lemma unitsMap_Gamma0Map_toHomUnits_eq_of_diag {l : ℕ} (hlN : l ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) (γ' : ↥(Gamma0 (N / l))) {j : ℤ}
    (hdiag : γ 1 1 = (γ' : SL(2, ℤ)) 1 1 - (γ' : SL(2, ℤ)) 1 0 * j) : ZMod.unitsMap
    (Nat.div_dvd_of_dvd hlN) ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) =
    (Gamma0Map (N / l)).toHomUnits γ' := by
  have hγ' : γ ∈ Gamma0 (N / l) := Gamma0_le_Gamma0_of_dvd (Nat.div_dvd_of_dvd hlN) hγ
  rw [← Gamma0Map_toHomUnits_of_dvd (Nat.div_dvd_of_dvd hlN) ⟨γ, hγ⟩ hγ']
  refine Units.ext ?_
  have h10 : (((γ' : SL(2, ℤ)) 1 0 : ℤ) : ZMod (N / l)) = 0 := Gamma0_mem.mp γ'.property
  rw [MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits, Gamma0Map_apply, Gamma0Map_apply,
    hdiag]
  push_cast
  rw [h10]
  ring

/-- **The descended cusp form carries the lowered nebentypus.** `cuspFormOfSmulSlashScaleGL`
produces a cusp form of level `N / l`; this identifies its nebentypus as the lowered character
`hfac.χ₀`, which is what makes the descent an eigenform statement rather than merely a level
statement. -/
theorem cuspFormOfSmulSlashScaleGL_mem_cuspFormCharSpace {l : ℕ} [NeZero l]
    (hlN : l ∣ N) (k : ℤ) {χ : DirichletCharacter ℂ N} (hfac : χ.FactorsThrough (N / l)) (f : ℍ → ℂ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hgχ : g ∈ cuspFormCharSpace k χ.toUnitHom)
    (hg : ⇑g = (l : ℂ) ^ (1 - k) • (f ∣[k] scaleGL l))
    (hT : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f)
    : cuspFormOfSmulSlashScaleGL l N hlN k χ.toUnitHom
    (fun _ hu ↦ MonoidHom.mem_ker.mp (DirichletCharacter.factorsThrough_iff_ker_unitsMap
      (Nat.div_dvd_of_dvd hlN) |>.mp hfac (MonoidHom.mem_ker.mpr hu))) f g hgχ hg hT ∈
      cuspFormCharSpace k hfac.χ₀.toUnitHom := by
  rw [mem_cuspFormCharSpace_iff_nebentypus]
  intro γ'
  rw [coe_cuspFormOfSmulSlashScaleGL]
  obtain ⟨i, j, c, γ, hc, hγ, hfactor, hdiag⟩ :=
    exists_eq_T_zpow_mul_conjScale_mul_T_zpow l N hlN (γ' : SL(2, ℤ)) γ'.property
  have hdet := det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨ModularGroup.T, rfl⟩)
  have hconj := slash_conjScale_eq_smul_of_slash_scaleGL (k := k) f γ hc
    (nebentypus_slash_scaleGL_of_mem_cuspFormCharSpace hgχ hg γ hγ)
  -- the label of the lift reduces to the label of `γ'`, so the two characters agree
  have hchar : (χ.toUnitHom ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂ) =
      (hfac.χ₀.toUnitHom ((Gamma0Map (N / l)).toHomUnits γ') : ℂ) := by
    conv_lhs => rw [hfac.eq_changeLevel]
    rw [DirichletCharacter.changeLevel_toUnitHom, MonoidHom.comp_apply,
      unitsMap_Gamma0Map_toHomUnits_eq_of_diag hlN hγ γ' hdiag]
  rw [hfactor, map_mul, map_mul, map_zpow, map_zpow,
    slash_zpow_mul_mul_zpow_eq_smul k f hdet hT hconj i j, hchar]

/-- **The level-lowering dichotomy.** For `l ∣ N`, a Dirichlet character `χ` of level `N`, and a
`T`-periodic `f : ℍ → ℂ` whose level-raise by `l` is a cusp form in `S_k(N, χ)`: *either* `χ`
factors through `N / l` and `f` is itself a cusp form in `S_k(N / l, χ↓)` for the lowered
character, *or* `f = 0`.

This is Miyake's Theorem 4.6.4. The two horns are `TauCeti.cuspFormOfSmulSlashScaleGL` with
`TauCeti.cuspFormOfSmulSlashScaleGL_mem_cuspFormCharSpace`, and
`TauCeti.eq_zero_of_not_forall_unitsMap_eq_one`; the case split is on the single proposition that
one assumes and the other negates. -/
theorem exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero {l : ℕ} [NeZero l]
    (hlN : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hgχ : g ∈ cuspFormCharSpace k χ.toUnitHom)
    (hg : ⇑g = (l : ℂ) ^ (1 - k) • (f ∣[k] scaleGL l))
    (hT : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    (∃ hfac : χ.FactorsThrough (N / l), ∃ F : CuspForm ((Gamma1 (N / l)).map (mapGL ℝ)) k, F ∈
      cuspFormCharSpace k hfac.χ₀.toUnitHom ∧ ⇑F = f) ∨ f = 0 := by
  classical
  by_cases hfac : χ.FactorsThrough (N / l)
  · exact .inl ⟨hfac, _,
      cuspFormOfSmulSlashScaleGL_mem_cuspFormCharSpace hlN k hfac f g hgχ hg hT,
      coe_cuspFormOfSmulSlashScaleGL l N hlN k χ.toUnitHom _ f g hgχ hg hT⟩
  · refine .inr (eq_zero_of_not_forall_unitsMap_eq_one hlN k ?_ f
      (nebentypus_slash_scaleGL_of_mem_cuspFormCharSpace hgχ hg) hT)
    exact fun h ↦ hfac ((DirichletCharacter.factorsThrough_iff_ker_unitsMap
      (Nat.div_dvd_of_dvd hlN)).mpr fun u hu ↦ MonoidHom.mem_ker.mpr
        (h u (MonoidHom.mem_ker.mp hu)))


end TauCeti

end
