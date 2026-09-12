/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Scalar
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Fourier coefficients of the Hecke operators at a prime power on `S_k(N, χ)`

The `Γ₀(N)` Hecke ring acts on `S_k(N, χ)` through `heckeRingHomCuspCharSpace`; at a prime `p`
the generator acts as the classical `Tₚ` (`HeckeSlash/Nebentypus/Prime/Basic.lean`), whose Fourier
coefficients are `a_m(Tₚ F) = a_{pm}(F) + χ(p) p^{k−1} a_{m/p}(F)`
(`HeckeSlash/Recurrence.lean`). Along the powers of a good prime `p ∤ N` the ring elements
`T_{p^r}` are the recurrence family `heckeTGeneratorRecGamma0`, with
`T_{p^{r+2}} = Tₚ T_{p^{r+1}} − p S_p T_{p^r}`, and the scalar coset `S_p` acts on the character
space by `χ(p) p^{k−2}` (`HeckeSlash/Nebentypus/Scalar.lean`). Unwinding that recurrence on
coefficients gives the classical formula: writing `c = χ(p) p^{k−1}`, for every index `m` prime
to `p`,

`a_{p^j m}(T_{p^r} F) = ∑_{i ≤ min j r} c^i · a_{p^{j+r−2i} m}(F)`,

the two-step recurrence between such sums being
`TauCeti.sum_range_min_add_two` (`Algebra/BigOperators/Finset/Range.lean`),

the prime-power case of Diamond–Shurman Proposition 5.3.1, and in particular
`a_m(T_{p^r} F) = a_{p^r m}(F)`. The composite operators are ordered products of these blocks
(`heckeTCompositeGamma0`), so this is the input for the coefficient formula at a general index
coprime to the level.

## Main results

* `HeckeRing.GL2.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_add_two` and its pointwise
  form `..._add_two_apply`: the ring's two-step recurrence on the character space.
* `HeckeRing.GL2.qExpansion_coeff_prime_pow_mul_heckeTGeneratorRecGamma0`: the formula above.
* `HeckeRing.GL2.qExpansion_coeff_heckeTGeneratorRecGamma0_of_not_dvd`:
  `a_m(T_{p^r} F) = a_{p^r m}(F)` at an index `m` prime to `p`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`),
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/FourierHecke.lean` —
`fourierCoeff_heckeT_ppow_period_one` and `fourierCoeff_heckeT_p_period_one`, which state the
divisor-sum form `a_m(T_{p^v} f) = ∑_{d ∣ gcd(m, p^v)} d^{k−1} χ(d) a_{m p^v / d²}(f)` for the
source's concretely-defined `heckeT_ppow`. Here the operator is the Hecke ring's own recurrence
family acting through `heckeRingHomCuspCharSpace`, so the formula is proved from the ring
recurrence and the prime case rather than from coset representatives, and it is stated at the
indices `p^j m` with `m` prime to `p`, where the divisor sum is the `min` sum above.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.3.1.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **The recurrence, transported to the character space.** For `p` coprime to `N`,
`T_{p^{r+2}} = Tₚ ∘ T_{p^{r+1}} − χ(p) p^{k−1} • T_{p^r}` as endomorphisms of `S_k(N, χ)`: the
image of `heckeTGeneratorRecGamma0_succ_succ` under the ring homomorphism, with the scalar coset
acting by `χ(p) p^{k−2}` (`heckeRingHomCuspCharSpace_heckeTScalarGamma0`), so that `p • S_p` acts
by `χ(p) p^{k−1}`. Only positivity of `p` is used. -/
theorem heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_add_two (hp : 0 < p)
    (hpN : Nat.Coprime p N) (r : ℕ) :
    heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 2)) =
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) *
          heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 1)) -
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) •
          heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p r) := by
  refine LinearMap.ext fun F ↦ ?_
  rw [heckeTGeneratorRecGamma0_succ_succ, map_sub, map_mul, map_mul, map_zsmul,
    heckeRingHomCuspCharSpace_heckeTScalarGamma0 k χ p hp hpN]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 2
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hk : k - 1 = k - 2 + 1 := by ring
  rw [hk, zpow_add_one₀ hp0]
  push_cast
  ring

/-- **The recurrence at a form**: `heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_add_two`
evaluated. This is the pointwise interface — the shape the coefficient formula below and the
eigenvalue recurrence of `Newforms/RingEigenvalue.lean` consume. -/
theorem heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_add_two_apply (hp : 0 < p)
    (hpN : Nat.Coprime p N) (F : cuspFormCharSpace k χ) (r : ℕ) :
    heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 2)) F =
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p)
          (heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 1)) F) -
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) •
          heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F := by
  rw [heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_add_two hp hpN r]
  rfl

/-- **`Tₚ` at an index prime to `p`** reads the coefficient at `p m`: the `p ∣ m` term of the
recurrence is absent. -/
theorem qExpansion_coeff_heckeTGeneratorGamma0_of_not_dvd (hp : p.Prime)
    (hpN : Nat.Coprime p N) (G : cuspFormCharSpace k χ) {m : ℕ} (hpm : ¬ p ∣ m) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) G :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p * m) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp G, heckeTCuspNat_def,
    qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_mem_cuspFormCharSpace k hp
      hpN χ G.2, ite_eq_right hpm, add_zero]

/-- **`Tₚ` at an index divisible by `p`**: `a_{p^{j+1} m}(Tₚ G) = a_{p^{j+2} m}(G) +
χ(p) p^{k−1} a_{p^j m}(G)`, the recurrence with both terms present. -/
theorem qExpansion_coeff_prime_pow_succ_mul_heckeTGeneratorGamma0 (hp : p.Prime)
    (hpN : Nat.Coprime p N) (G : cuspFormCharSpace k χ) (m j : ℕ) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) G :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ (j + 1) * m) =
      (qExpansion 1 (G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ (j + 2) * m) +
        (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 (G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ j * m) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdvd : p ∣ p ^ (j + 1) * m := dvd_mul_of_dvd_left (dvd_pow_self p j.succ_ne_zero) m
  have hdiv : p ^ (j + 1) * m / p = p ^ j * m := by
    rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  rw [coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp G, heckeTCuspNat_def,
    qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_mem_cuspFormCharSpace k hp
      hpN χ G.2, ite_eq_left hdvd, hdiv, ← mul_assoc, ← pow_succ']

/-- The formula at `r = 1`, where the ring element is the generator `Tₚ` itself: one term at an
index prime to `p`, two at a multiple of `p`. -/
private theorem qExpansion_coeff_prime_pow_mul_heckeTGeneratorGamma0 (hp : p.Prime)
    (hpN : Nat.Coprime p N) (F : cuspFormCharSpace k χ) {m : ℕ} (hpm : ¬ p ∣ m) (j : ℕ) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ j * m) =
      ∑ i ∈ Finset.range (min j 1 + 1),
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) ^ i *
          (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff
            (p ^ (j + 1 - 2 * i) * m) := by
  rcases j with _ | j
  · -- `p ∤ m`: one term, at the index `p m`
    have hidx : p * m = p ^ (0 + 1 - 2 * 0) * m := by simp
    rw [pow_zero, one_mul, qExpansion_coeff_heckeTGeneratorGamma0_of_not_dvd hp hpN F hpm, hidx]
    simp
  · -- `p ∣ p^{j+1} m`: two terms, at `p^{j+2} m` and `p^j m`
    have hmin : min (j + 1) 1 + 1 = 2 := by omega
    have hidx₁ : j + 1 + 1 - 2 * 0 = j + 2 := by omega
    have hidx₂ : j + 1 + 1 - 2 * 1 = j := by omega
    rw [qExpansion_coeff_prime_pow_succ_mul_heckeTGeneratorGamma0 hp hpN F m j, hmin,
      Finset.sum_range_succ, Finset.sum_range_one, hidx₁, hidx₂]
    simp

/-- **The prime-power coefficient formula on `S_k(N, χ)`.** For a good prime `p ∤ N`, an index `m`
prime to `p` and all `j`, `r`, writing `c = χ(p) p^{k−1}`,
`a_{p^j m}(T_{p^r} F) = ∑_{i ≤ min j r} c^i · a_{p^{j+r−2i} m}(F)`
(Diamond–Shurman Proposition 5.3.1 at a prime power). -/
theorem qExpansion_coeff_prime_pow_mul_heckeTGeneratorRecGamma0 (hp : p.Prime)
    (hpN : Nat.Coprime p N) (F : cuspFormCharSpace k χ) {m : ℕ} (hpm : ¬ p ∣ m) (r j : ℕ) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ j * m) =
      ∑ i ∈ Finset.range (min j r + 1),
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) ^ i *
          (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff
            (p ^ (j + r - 2 * i) * m) := by
  induction r using Nat.twoStepInduction generalizing j with
  | zero =>
    rw [heckeTGeneratorRecGamma0_zero, map_one, Module.End.one_apply]
    simp
  | one =>
    rw [heckeTGeneratorRecGamma0_one]
    exact qExpansion_coeff_prime_pow_mul_heckeTGeneratorGamma0 hp hpN F hpm j
  | more r ih1 ih2 =>
    rw [heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_add_two_apply hp.pos hpN F r,
      Submodule.coe_sub, Submodule.coe_smul, FunLike.coe_sub, FunLike.coe_smul,
      TauCeti.qExpansion_coeff_sub_smul
        (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos
          (TauCeti.one_mem_strictPeriods_Gamma1_map _))
        (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos
          (TauCeti.one_mem_strictPeriods_Gamma1_map _))]
    rcases j with _ | j
    · -- `p ∤ m`: the recurrence reads the coefficient at `p m`, which is the `j = 1` instance
      have h1 := ih1 0
      have h2 := ih2 1
      rw [pow_zero, one_mul] at h1
      rw [pow_one] at h2
      rw [pow_zero, one_mul, qExpansion_coeff_heckeTGeneratorGamma0_of_not_dvd hp hpN _ hpm, h2,
        h1]
      exact TauCeti.sum_range_min_zero
        (fun t ↦ (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ t * m))
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) r
    · -- both terms of the recurrence are present, and the four sums recombine by
      -- `TauCeti.sum_range_min_add_two`
      rw [qExpansion_coeff_prime_pow_succ_mul_heckeTGeneratorGamma0 hp hpN _ m j, ih2 (j + 2),
        ih2 j, ih1 (j + 1)]
      have h := TauCeti.sum_range_min_add_two
        (fun t ↦ (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ t * m))
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) j r
      linear_combination h

/-- **At an index prime to `p`, `T_{p^r}` reads the coefficient at `p^r m`**:
`a_m(T_{p^r} F) = a_{p^r m}(F)`, the `j = 0` case of the prime-power formula. -/
theorem qExpansion_coeff_heckeTGeneratorRecGamma0_of_not_dvd (hp : p.Prime)
    (hpN : Nat.Coprime p N) (F : cuspFormCharSpace k χ) {m : ℕ} (hpm : ¬ p ∣ m) (r : ℕ) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ r * m) := by
  have h := qExpansion_coeff_prime_pow_mul_heckeTGeneratorRecGamma0 hp hpN F hpm r 0
  simpa using h

end HeckeRing.GL2
