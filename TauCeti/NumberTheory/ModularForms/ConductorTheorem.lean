/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The level-lowering dichotomy: the character arithmetic that precedes the descent

Let `l ∣ N`, let `χ` be a Dirichlet character mod `N`, and let `f` be a `T`-periodic function on
`ℍ` whose level-raise by `l` is a cusp form in `S_k(N, χ)`. The conductor theorem says that
either `χ` factors through `N / l` and `f` is itself a cusp form of the lowered level, or `f = 0`.

This file collects the character-and-unit arithmetic that argument runs on, ahead of the descent
itself:

* a **unit witnessing non-factorisation** — if `χ` does not factor through `d ∣ N`, some unit is
  trivial modulo `d` yet non-trivial under `χ`;
* **character separation within a coset** — every unit has a partner with the same reduction
  modulo `d` but a different character value, so `χ` cannot be read off the reduction alone;
* the **integer congruence** that turns equal reductions into a divisibility, which is how the
  unit bookkeeping reaches the matrix entries.

Everything else the dichotomy needs is deliberately elsewhere. The `Γ₀(N)` element of prescribed
lower-left entry and diamond label is `CongruenceSubgroup.gamma0Twist`
(`CongruenceSubgroups/Basic.lean`), with `gamma0Twist_apply_one_zero`,
`gamma0Twist_apply_one_one` and `Gamma0Map_toHomUnits_gamma0Twist`; for a unit `u` it is used at
`p = (u : ZMod N).val`, which is coprime to `N` by `ZMod.val_coe_unit_coprime`. The
two-multiplier vanishing principle is Mathlib's `smul_left_injective` applied in `ℍ → ℂ`. The
three analytic conditions are `TauCeti.slash_conjScale_eq_smul_of_slash_scaleGL` and
`TauCeti.mdifferentiable_of_comp_scaleGL_smul` in `Degeneracy.lean`, and
`TauCeti.isZeroAt_of_smul_slash_scaleGL_eq` in `CuspDescent.lean`, all three stated for an `f`
that is only a function — which is exactly this theorem's situation.

## Main results

* `TauCeti.exists_unit_of_not_factorsThrough`: the unit witnessing non-factorisation.
* `TauCeti.exists_alt_unit_in_coset_with_char_separation`: the character is not a function of the
  reduction modulo `d`.
* `TauCeti.natCast_val_sub_dvd_of_unitsMap_eq`: equal reductions give an integer congruence.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean`, declarations
`exists_unit_of_not_factorsThrough` (:542),
`exists_alt_unit_in_coset_with_char_separation` (:656) and
`natCast_val_sub_dvd_of_unitsMap_eq` (:665).

Three deliberate departures from the source. The source builds its own `Γ₀(N)` lift of a unit
(`gamma0LiftLowerLeftN`, :564, with entry lemmas at :590-:607 and :688) and its own
two-multiplier vanishing lemma (`fun_eq_zero_of_two_multipliers`, :555); neither is ported,
because this repository already has `CongruenceSubgroup.gamma0Twist` and Mathlib already has
`smul_left_injective`. The source also reaches the coset form through an intermediate shift form
(`exists_kernel_unit_with_char_shift`, :646); since each is a one-line consequence of the other,
only the coset form is ported and it is proved directly. The source states
`natCast_val_sub_dvd_of_unitsMap_eq` only for the reduction modulo `N / l`; it is stated here for
an arbitrary divisor `d ∣ N`, which is all its proof uses. Finally, the source states the two
character lemmas for `ℂ`-valued characters; they are stated here for any `CommMonoidWithZero`
target, which is the generality of the Mathlib lemma they run on
(`DirichletCharacter.factorsThrough_iff_ker_unitsMap`), and which lets this file import only
`Mathlib.NumberTheory.DirichletCharacter.Basic`.

## References

* [Miyake, *Modular forms*][miyake1989], Theorem 4.6.4.
-/

public section

namespace TauCeti

/-- **A unit witnessing non-factorisation.** If `χ` mod `N` does not factor through `d ∣ N`, then
some unit is trivial modulo `d` while `χ` is non-trivial on it: the kernel of the reduction is not
contained in the kernel of `χ`. -/
theorem exists_unit_of_not_factorsThrough {R : Type*} [CommMonoidWithZero R] {N : ℕ} [NeZero N]
    {d : ℕ} (hd : d ∣ N) {χ : DirichletCharacter R N} (h_not_fac : ¬ χ.FactorsThrough d) :
    ∃ u : (ZMod N)ˣ, ZMod.unitsMap hd u = 1 ∧ χ.toUnitHom u ≠ 1 := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd] at h_not_fac
  obtain ⟨u, hu_ker, hu_chi⟩ := SetLike.not_le_iff_exists.mp h_not_fac
  exact ⟨u, MonoidHom.mem_ker.mp hu_ker, hu_chi ∘ MonoidHom.mem_ker.mpr⟩

/-- **Character separation within a coset.** Under non-factorisation, every `u` has a partner `u'`
with the same reduction modulo `d` but a different character value — so the character cannot be
read off the reduction alone. -/
theorem exists_alt_unit_in_coset_with_char_separation {R : Type*} [CommMonoidWithZero R] {N : ℕ}
    [NeZero N] {d : ℕ} (hd : d ∣ N) {χ : DirichletCharacter R N}
    (h_not_fac : ¬ χ.FactorsThrough d) (u : (ZMod N)ˣ) :
    ∃ u' : (ZMod N)ˣ,
      ZMod.unitsMap hd u' = ZMod.unitsMap hd u ∧ χ.toUnitHom u' ≠ χ.toUnitHom u := by
  obtain ⟨v, hv_ker, hv_chi⟩ := exists_unit_of_not_factorsThrough hd h_not_fac
  exact ⟨u * v, by rw [map_mul, hv_ker, mul_one],
    by rw [map_mul, Ne, mul_eq_left]; exact hv_chi⟩

/-- **From equal reductions to an integer congruence.** Two units with the same image under the
reduction `(ZMod N)ˣ → (ZMod d)ˣ` along `d ∣ N` have representatives congruent modulo `d`, as
integers. This is the arithmetic bridge between the unit bookkeeping and the matrix entries; the
dichotomy applies it at `d = N / l`. -/
theorem natCast_val_sub_dvd_of_unitsMap_eq {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    (u u' : (ZMod N)ˣ) (h_eq : ZMod.unitsMap hd u = ZMod.unitsMap hd u') :
    (d : ℤ) ∣ (((u : ZMod N).val : ℤ) - ((u' : ZMod N).val : ℤ)) := by
  have h_cast_eq : ZMod.castHom hd (ZMod d) (u : ZMod N) =
      ZMod.castHom hd (ZMod d) (u' : ZMod N) := by
    have hh := congr_arg Units.val h_eq
    rwa [ZMod.unitsMap_val, ZMod.unitsMap_val] at hh
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val (u : ZMod N), ZMod.natCast_val (u' : ZMod N),
    ← ZMod.castHom_apply (h := hd) (u : ZMod N), ← ZMod.castHom_apply (h := hd) (u' : ZMod N),
    h_cast_eq]
  ring

end TauCeti
