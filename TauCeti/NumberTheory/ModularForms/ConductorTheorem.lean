/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CuspDescent
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The level-lowering dichotomy: the pieces that precede the descent

Let `l ∣ N`, let `χ` be a Dirichlet character mod `N`, and let `f` be a `T`-periodic function on
`ℍ` whose level-raise by `l` is a cusp form in `S_k(N, χ)`. The conductor theorem says that
either `χ` factors through `N / l` and `f` is itself a cusp form of the lowered level, or `f = 0`.

This file collects the arithmetic input to that argument, ahead of the descent itself:

* a **unit witnessing non-factorisation** — if `χ` does not factor through `d ∣ N`, some unit is
  trivial modulo `d` yet non-trivial under `χ`;
* a **two-multiplier vanishing** principle — a function that is an eigenvector of one slash with
  two different eigenvalues is zero, which is how the second branch of the dichotomy is reached;
* a **controlled lift** `gamma0LiftLowerLeftN` of a unit to `Γ₀(N)` whose lower-left entry is
  exactly `N`, together with its four matrix entries and its diamond label.

The three analytic conditions the descent needs are not here and are not ported: they are
`TauCeti.slash_conjScale_eq_smul_of_slash_scaleGL` and
`TauCeti.mdifferentiable_of_comp_scaleGL_smul` in `Degeneracy.lean`, and
`TauCeti.isZeroAt_of_smul_slash_scaleGL_eq` in `CuspDescent.lean`, all three stated for an `f`
that is only a function — which is exactly this theorem's situation.

## Main results

* `TauCeti.exists_unit_of_not_factorsThrough`: the unit witnessing non-factorisation.
* `TauCeti.fun_eq_zero_of_two_multipliers`: two distinct multipliers force vanishing.
* `TauCeti.gamma0LiftLowerLeftN`: the controlled `Γ₀(N)` lift, with
  `TauCeti.toHomUnits_gamma0LiftLowerLeftN` recovering the unit it lifts.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean`, declarations
`exists_unit_of_not_factorsThrough` (:542), `fun_eq_zero_of_two_multipliers` (:555),
`gamma0LiftLowerLeftN` (:564) and its entry lemmas (:590-:607).

The source states the diamond label through its own `Gamma0MapUnits`; this repository has no such
abbreviation — deliberately, as `Fricke/Conjugation.lean` records — so the label is read through
`CongruenceSubgroup.Gamma0Map`'s `toHomUnits` instead, and no second unit-valued map is
introduced.

## References

* [Miyake, *Modular forms*][miyake1989], Theorem 4.6.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Function
open scoped Manifold MatrixGroups ModularForm Pointwise

namespace TauCeti

/-- **A unit witnessing non-factorisation.** If `χ` mod `N` does not factor through `d ∣ N`, then
some unit is trivial modulo `d` while `χ` is non-trivial on it: the kernel of the reduction is not
contained in the kernel of `χ`. -/
theorem exists_unit_of_not_factorsThrough {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    {χ : DirichletCharacter ℂ N} (h_not_fac : ¬ χ.FactorsThrough d) :
    ∃ u : (ZMod N)ˣ, ZMod.unitsMap hd u = 1 ∧ χ.toUnitHom u ≠ 1 := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd] at h_not_fac
  obtain ⟨u, hu_ker, hu_chi⟩ := SetLike.not_le_iff_exists.mp h_not_fac
  exact ⟨u, MonoidHom.mem_ker.mp hu_ker, hu_chi ∘ MonoidHom.mem_ker.mpr⟩

/-- **Two distinct multipliers force vanishing.** If `f ∣[k] M` equals both `c₁ • f` and `c₂ • f`
with `c₁ ≠ c₂`, then `f = 0`. This is how the dichotomy reaches its second branch: a character
that fails to descend produces two incompatible multipliers for the same slash. -/
theorem fun_eq_zero_of_two_multipliers (k : ℤ) (f : ℍ → ℂ) (M : GL (Fin 2) ℝ)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂) (h₁ : f ∣[k] M = c₁ • f) (h₂ : f ∣[k] M = c₂ • f) : f = 0 := by
  have h_diff : (c₁ - c₂) • f = 0 := by rw [sub_smul, h₁.symm.trans h₂, sub_self]
  exact (smul_eq_zero.mp h_diff).resolve_left (sub_ne_zero.mpr hne)

/-- **The controlled `Γ₀(N)` lift of a unit.** For `u : (ZMod N)ˣ` this is the Bézout matrix
`!![a, b; N, e]` with `e` a lift of `u`, `a` a lift of `u⁻¹`, and `b = (a * e - 1) / N`. Its
lower-left entry is exactly `N`, which is what lets it be used where a `Γ₀(N)` element of
prescribed shape is needed. -/
@[expose]
noncomputable def gamma0LiftLowerLeftN (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ↥(Gamma0 N) := by
  let e : ℤ := ((u.val : ZMod N).val : ℤ)
  let a : ℤ := ((u⁻¹.val : ZMod N).val : ℤ)
  have h_ae : ((a * e : ℤ) : ZMod N) = 1 := by
    change (((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ)) : ℤ) : ZMod N) = 1
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have h_dvd : (N : ℤ) ∣ (a * e - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [show ((a : ZMod N) * (e : ZMod N) - 1 : ZMod N) = ((a * e : ℤ) : ZMod N) - 1 by
        push_cast; ring, h_ae]
    ring
  let b : ℤ := (a * e - 1) / (N : ℤ)
  refine ⟨⟨!![a, b; (N : ℤ), e], ?det⟩, ?gamma0⟩
  · rw [Matrix.det_fin_two_of]
    change a * e - b * (N : ℤ) = 1
    linarith [Int.ediv_mul_cancel h_dvd]
  · exact Gamma0_mem.mpr (by simp)

/-- The lower-left entry of the controlled lift is `N`. -/
@[simp]
theorem gamma0LiftLowerLeftN_lower_left (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 0 : ℤ) = (N : ℤ) := rfl

/-- The lower-right entry of the controlled lift is the chosen lift of `u`. -/
@[simp]
theorem gamma0LiftLowerLeftN_lower_right (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 1 : ℤ) = ((u.val : ZMod N).val : ℤ) := rfl

/-- The upper-left entry of the controlled lift is the chosen lift of `u⁻¹`. -/
@[simp]
theorem gamma0LiftLowerLeftN_upper_left (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 0 : ℤ) = ((u⁻¹.val : ZMod N).val : ℤ) := rfl

/-- **The controlled lift has diamond label `u`.** Read through `Gamma0Map`'s unit-valued
refinement, the lift recovers exactly the unit it was built from. -/
@[simp]
theorem toHomUnits_gamma0LiftLowerLeftN (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (Gamma0Map N).toHomUnits (gamma0LiftLowerLeftN N u) = u := by
  apply Units.ext
  change ((((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 1 : ℤ)) : ZMod N) = (u : ZMod N)
  rw [gamma0LiftLowerLeftN_lower_right]
  push_cast
  rw [ZMod.natCast_zmod_val]

/-- The upper-right entry of the controlled lift is the Bézout coefficient `(a * e - 1) / N`. -/
@[simp]
theorem gamma0LiftLowerLeftN_upper_right (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 1 : ℤ) =
      (((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) / (N : ℤ) := rfl

/-- **A kernel unit that shifts the character.** If `χ` does not factor through `d`, then for any
`u` there is a `v` trivial modulo `d` with `χ (u * v) ≠ χ u`: multiplying by the witness of
non-factorisation moves the character value while fixing the reduction. -/
theorem exists_kernel_unit_with_char_shift {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    {χ : DirichletCharacter ℂ N} (h_not_fac : ¬ χ.FactorsThrough d) (u : (ZMod N)ˣ) :
    ∃ v : (ZMod N)ˣ, ZMod.unitsMap hd v = 1 ∧ χ.toUnitHom (u * v) ≠ χ.toUnitHom u := by
  obtain ⟨v, hv_ker, hv_chi⟩ := exists_unit_of_not_factorsThrough hd h_not_fac
  refine ⟨v, hv_ker, fun h ↦ hv_chi <| mul_left_cancel <|
    show χ.toUnitHom u * χ.toUnitHom v = χ.toUnitHom u * 1 by rw [← map_mul, h, mul_one]⟩

/-- **Character separation within a coset.** Under non-factorisation, every `u` has a partner `u'`
with the same reduction modulo `d` but a different character value — so the character cannot be
read off the reduction alone. -/
theorem exists_alt_unit_in_coset_with_char_separation {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    {χ : DirichletCharacter ℂ N} (h_not_fac : ¬ χ.FactorsThrough d) (u : (ZMod N)ˣ) :
    ∃ u' : (ZMod N)ˣ,
      ZMod.unitsMap hd u' = ZMod.unitsMap hd u ∧ χ.toUnitHom u' ≠ χ.toUnitHom u := by
  obtain ⟨v, hv_ker, hv_chi⟩ := exists_kernel_unit_with_char_shift hd h_not_fac u
  exact ⟨u * v, by rw [map_mul, hv_ker, mul_one], hv_chi⟩

/-- **From equal reductions to an integer congruence.** Two units with the same image under the
reduction `(ZMod N)ˣ → (ZMod (N / l))ˣ` have representatives congruent modulo `N / l`, as integers.
This is the arithmetic bridge between the unit bookkeeping and the matrix entries. -/
theorem natCast_val_sub_dvd_of_unitsMap_eq {N l : ℕ} [NeZero N] [NeZero l] (h_dvd : l ∣ N)
    (u u' : (ZMod N)ˣ)
    (h_eq : ZMod.unitsMap ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ u =
      ZMod.unitsMap ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ u') :
    ((N / l : ℕ) : ℤ) ∣ (((u : ZMod N).val : ℤ) - ((u' : ZMod N).val : ℤ)) := by
  have hNl_dvd_N : (N / l) ∣ N := ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩
  have h_cast_eq : ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u : ZMod N) =
      ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u' : ZMod N) := by
    have hh := congr_arg Units.val h_eq
    rwa [ZMod.unitsMap_val, ZMod.unitsMap_val] at hh
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val (u : ZMod N), ZMod.natCast_val (u' : ZMod N),
    show (ZMod.cast ((u : ZMod N) : ZMod N) : ZMod (N / l)) =
      ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u : ZMod N) from rfl,
    show (ZMod.cast ((u' : ZMod N) : ZMod N) : ZMod (N / l)) =
      ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u' : ZMod N) from rfl, h_cast_eq]
  ring

end TauCeti
