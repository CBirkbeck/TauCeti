/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ConductorDichotomy
public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Basic

/-!
# The factor dichotomy of the coprime sieve

Let `f ∈ S_k(Γ₁(N), χ)` vanish at every index coprime to `p L`, for a prime `p ∣ N` and a
squarefree `L` coprime to `p` whose primes divide `N`. Either `f` already vanishes at every index
coprime to `L`, or the nebentypus `χ` is the pull-back of a character modulo `N / p`. This is
the case split of Miyake's proof of Lemma 4.6.8 (the Main Lemma of Diamond–Shurman §5.7, per
character): in the second case the descent along `p` produces a form of level `N / p`, and in
the first the prime `p` needs no descent at all.

The coprime filter of `f` (`Newforms/CoprimeFilter/Basic.lean`) is a form `G` of level `L N`
carrying the coefficients of `f` at the indices coprime to `L` and supported on the multiples of
`p`; the level-lowering dichotomy (`ConductorDichotomy.lean`) either finds `G` to be a
level-raise from `L N / p`, so that the pulled-back character factors through `L N / p` and, by
the conductor, `χ` factors through `N / p`, or forces `G = 0`, which is the vanishing of `f`.

## Main results

* `TauCeti.qExpansion_coeff_eq_zero_of_coprime_or_exists_eq_comp_unitsMap`: the dichotomy.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/InductiveStep.lean`,
`miyake_4_6_8_factor_dichotomy`. The source's private conductor lemmas
(`conductor_dvd_of_factorsThrough`, `factorsThrough_of_conductor_dvd`, `conductor_changeLevel`)
are Mathlib's `DirichletCharacter.conductor_dvd_of_mem_conductorSet`,
`mem_conductorSet_iff_conductor_dvd` and `conductor_changeLevel`.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.8.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- A character modulo `N` whose lift to level `L N` factors through `L N / p`, for `p ∣ N`
prime and `L` coprime to `p`, factors through `N / p`: `changeLevel` preserves the conductor,
which then divides `gcd (N, L N / p) = N / p`. -/
private theorem factorsThrough_div_of_changeLevel_factorsThrough {p L : ℕ} [NeZero (L * N)]
    (hpN : p ∣ N) (hpL : Nat.Coprime p L) {ψ : DirichletCharacter ℂ N}
    (hfac : (DirichletCharacter.changeLevel (Nat.dvd_mul_left N L) ψ).FactorsThrough
      (L * N / p)) :
    ψ.FactorsThrough (N / p) := by
  have hN : N = p * (N / p) := (Nat.mul_div_cancel' hpN).symm
  have hc : ψ.conductor ∣ L * (N / p) := by
    have := DirichletCharacter.conductor_dvd_of_mem_conductorSet _ hfac
    rwa [DirichletCharacter.conductor_changeLevel, Nat.mul_div_assoc L hpN] at this
  have hgcd : Nat.gcd (p * (N / p)) (L * (N / p)) = N / p := by
    rw [Nat.gcd_mul_right, hpL.gcd_eq_one, one_mul]
  exact (DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ (Nat.div_dvd_of_dvd hpN)).mpr
    (hgcd ▸ Nat.dvd_gcd (hN ▸ ψ.conductor_dvd_level) hc)

/-- **The factor dichotomy.** For `f ∈ S_k(Γ₁(N), χ)` vanishing at every index coprime to `p L`,
with `p ∣ N` prime and `L` squarefree, coprime to `p`, with primes dividing `N`: either `f`
vanishes at every index coprime to `L`, or `χ` is the pull-back of a character modulo `N / p`. -/
theorem qExpansion_coeff_eq_zero_of_coprime_or_exists_eq_comp_unitsMap (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {p L : ℕ}
    (hp : p.Prime) (hpN : p ∣ N) (hL : Squarefree L) (hLN : L.primeFactors ⊆ N.primeFactors)
    (hpL : Nat.Coprime p L) (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    (∀ n, Nat.Coprime n L → (qExpansion 1 f).coeff n = 0) ∨
      ∃ χ₀ : (ZMod (N / p))ˣ →* ℂˣ, χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (L * N) := ⟨Nat.mul_ne_zero hL.ne_zero (NeZero.ne N)⟩
  have hpLN : p ∣ L * N := dvd_mul_of_dvd_right hpN L
  have hNLN : N ∣ L * N := Nat.dvd_mul_left N L
  obtain ⟨G, hGχ, hGsupp, hGcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansionSupportedOnDvd_of_squarefree χ hf hp hL hLN hvan
  obtain ⟨φ, hGφ, hφT⟩ :=
    CuspForm.exists_eq_smul_slash_scaleGL_and_slash_T_eq_of_qExpansionSupportedOnDvd G hGsupp
  -- the nebentypus of `G` is the level-`L N` lift of `χ`, as a Dirichlet character
  set ψ : DirichletCharacter ℂ N := MulChar.ofUnitHom χ with hψ
  have hψχ : ψ.toUnitHom = χ := MulChar.equivToUnitHom.apply_symm_apply χ
  have hGψ : G ∈ cuspFormCharSpace k (DirichletCharacter.changeLevel hNLN ψ).toUnitHom := by
    rwa [DirichletCharacter.changeLevel_toUnitHom, hψχ]
  rcases exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero hpLN k _ φ G hGψ hGφ hφT with
    ⟨hfac, -, -, -⟩ | hφ0
  · -- `χ` lifted to level `L N` factors through `L N / p`, so `χ` factors through `N / p`
    right
    have hfac' := factorsThrough_div_of_changeLevel_factorsThrough hpN hpL hfac
    refine ⟨hfac'.χ₀.toUnitHom, ?_⟩
    rw [← hψχ]
    conv_lhs => rw [hfac'.eq_changeLevel]
    rw [DirichletCharacter.changeLevel_toUnitHom]
  · -- `G = 0`: the coefficients of `f` at the indices coprime to `L` are those of `G`
    left
    intro n hn
    have hG0 : (⇑G : ℍ → ℂ) = 0 := by rw [hGφ, hφ0, SlashAction.zero_slash, smul_zero]
    have h := hGcoeff n
    rw [hG0, qExpansion_zero, map_zero, ite_eq_left hn] at h
    exact h.symm

end TauCeti
