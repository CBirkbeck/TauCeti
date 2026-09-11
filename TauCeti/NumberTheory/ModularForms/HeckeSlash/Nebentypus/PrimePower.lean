/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimePower
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Scalar
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence

/-!
# Fourier coefficients of the Hecke operators at a prime power on `S_k(N, χ)`

The `Γ₀(N)` Hecke ring acts on `S_k(N, χ)` through `heckeRingHomCuspCharSpace`; at a prime `p`
the generator acts as the classical `Tₚ` (`HeckeSlash/Nebentypus/Prime.lean`), whose Fourier
coefficients are `a_m(Tₚ F) = a_{pm}(F) + χ(p) p^{k−1} a_{m/p}(F)`
(`HeckeSlash/Recurrence.lean`). Along the powers of a good prime `p ∤ N` the ring elements
`T_{p^r}` are the recurrence family `heckeTGeneratorRecGamma0`, with
`T_{p^{r+2}} = Tₚ T_{p^{r+1}} − p S_p T_{p^r}`, and the scalar coset `S_p` acts on the character
space by `χ(p) p^{k−2}` (`HeckeSlash/Nebentypus/Scalar.lean`). Unwinding that recurrence on
coefficients gives the classical formula: writing `c = χ(p) p^{k−1}`, for every index `m` prime
to `p`,

`a_{p^j m}(T_{p^r} F) = ∑_{i ≤ min j r} c^i · a_{p^{j+r−2i} m}(F)`,

the prime-power case of Diamond–Shurman Proposition 5.3.1, and in particular
`a_m(T_{p^r} F) = a_{p^r m}(F)`. The composite operators are ordered products of these blocks
(`heckeTCompositeGamma0`), so this is the input for the coefficient formula at a general index
coprime to the level.

## Main results

* `HeckeRing.GL2.qExpansion_coeff_prime_pow_mul_heckeTGeneratorRecGamma0`: the formula above.
* `HeckeRing.GL2.qExpansion_coeff_heckeTGeneratorRecGamma0_of_not_dvd`:
  `a_m(T_{p^r} F) = a_{p^r m}(F)` at an index `m` prime to `p`.

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

/-- **The recurrence, transported to the character space.** For `p ∤ N`,
`T_{p^{r+2}} F = Tₚ (T_{p^{r+1}} F) − χ(p) p^{k−1} • T_{p^r} F`: the image of
`heckeTGeneratorRecGamma0_succ_succ` under the ring homomorphism, with `p • S_p` acting by
`χ(p) p^{k−1}`. -/
theorem heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_add_two (hp : p.Prime)
    (hpN : Nat.Coprime p N) (F : cuspFormCharSpace k χ) (r : ℕ) :
    heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 2)) F =
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p)
          (heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 1)) F) -
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) •
          heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F := by
  rw [heckeTGeneratorRecGamma0_succ_succ, map_sub, map_mul, map_mul, map_zsmul,
    heckeRingHomCuspCharSpace_heckeTScalarGamma0 k χ p hp.pos hpN]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 2
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hk : k - 1 = k - 2 + 1 := by ring
  rw [hk, zpow_add_one₀ hp0]
  push_cast
  ring

omit [NeZero N] in
/-- The coefficients of a difference `x − c • y` in the character space. -/
private theorem qExpansion_coeff_coe_sub_smul (x y : cuspFormCharSpace k χ) (c : ℂ) (n : ℕ) :
    (qExpansion 1 ((x - c • y : cuspFormCharSpace k χ) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n =
      (qExpansion 1 (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n -
        c * (qExpansion 1 (y : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n := by
  rw [Submodule.coe_sub, Submodule.coe_smul, FunLike.coe_sub,
    ModularForm.qExpansion_sub one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _),
    FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _), map_sub,
    map_smul, smul_eq_mul]

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

/-- The index shift the two-step recurrence performs on the sums, on an abstract sequence: with
`S j r = ∑_{i ≤ min j r} c^i a (j + r − 2i)`,
`S (j+2) (r+1) + c · S j (r+1) = S (j+1) (r+2) + c · S (j+1) r`.
Every one of the four sums is a sum of `A i = c^i a (j + r + 3 − 2i)`, the two scalar multiples
with the index shifted by one, and the upper limits pair up:
`min j (r+1) + 1 = min (j+1) (r+2)` and `min (j+1) r + 1 = min (j+2) (r+1)`. So both sides are
the same pair of sums with the `i = 0` term of one of them removed. -/
private theorem sum_range_min_add_two (a : ℕ → ℂ) (c : ℂ) (j r : ℕ) :
    (∑ i ∈ Finset.range (min (j + 2) (r + 1) + 1), c ^ i * a (j + 2 + (r + 1) - 2 * i)) +
        c * ∑ i ∈ Finset.range (min j (r + 1) + 1), c ^ i * a (j + (r + 1) - 2 * i) =
      (∑ i ∈ Finset.range (min (j + 1) (r + 2) + 1), c ^ i * a (j + 1 + (r + 2) - 2 * i)) +
        c * ∑ i ∈ Finset.range (min (j + 1) r + 1), c ^ i * a (j + 1 + r - 2 * i) := by
  set A : ℕ → ℂ := fun i ↦ c ^ i * a (j + r + 3 - 2 * i) with hA
  -- a sum whose index reads `t - 2 i` with `t = j + r + 3` is a sum of `A`
  have eA : ∀ t n : ℕ, t = j + r + 3 →
      ∑ i ∈ Finset.range n, c ^ i * a (t - 2 * i) = ∑ i ∈ Finset.range n, A i := by
    rintro t n rfl
    rfl
  -- a scalar multiple of a sum whose index reads `t - 2 i` with `t + 2 = j + r + 3` is a sum of
  -- `A` with the index shifted by one
  have eshift : ∀ t n : ℕ, t + 2 = j + r + 3 →
      c * ∑ i ∈ Finset.range n, c ^ i * a (t - 2 * i) = ∑ i ∈ Finset.range n, A (i + 1) := by
    intro t n ht
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hA]
    rw [show j + r + 3 - 2 * (i + 1) = t - 2 * i by omega, ← mul_assoc, ← pow_succ']
  -- the shifted sums, as sums of `A` with the `i = 0` term removed
  have hsh : ∀ n : ℕ, ∑ i ∈ Finset.range n, A (i + 1) =
      (∑ i ∈ Finset.range (n + 1), A i) - A 0 := by
    intro n
    rw [Finset.sum_range_succ' A n]
    ring
  rw [eA (j + 2 + (r + 1)) _ (by omega), eA (j + 1 + (r + 2)) _ (by omega),
    eshift (j + (r + 1)) _ (by omega), eshift (j + 1 + r) _ (by omega), hsh, hsh,
    show min j (r + 1) + 1 + 1 = min (j + 1) (r + 2) + 1 by omega,
    show min (j + 1) r + 1 + 1 = min (j + 2) (r + 1) + 1 by omega]
  ring

/-- The recombination at `j = 0`, where the recurrence contributes only two terms:
`S 1 (r+1) − c · S 0 r = S 0 (r+2)`, both sides being `a (r+2)`. -/
private theorem sum_range_min_zero (a : ℕ → ℂ) (c : ℂ) (r : ℕ) :
    (∑ i ∈ Finset.range (min 1 (r + 1) + 1), c ^ i * a (1 + (r + 1) - 2 * i)) -
        c * ∑ i ∈ Finset.range (min 0 r + 1), c ^ i * a (0 + r - 2 * i) =
      ∑ i ∈ Finset.range (min 0 (r + 2) + 1), c ^ i * a (0 + (r + 2) - 2 * i) := by
  rw [show min 1 (r + 1) + 1 = 2 by omega, show min 0 (r + 2) + 1 = 1 by omega,
    show min 0 r + 1 = 1 by omega, Finset.sum_range_succ, Finset.sum_range_one,
    Finset.sum_range_one, Finset.sum_range_one, show 1 + (r + 1) - 2 * 0 = r + 2 by omega,
    show 1 + (r + 1) - 2 * 1 = r by omega, show 0 + (r + 2) - 2 * 0 = r + 2 by omega,
    show 0 + r - 2 * 0 = r by omega]
  ring

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
  · rw [pow_zero, one_mul, qExpansion_coeff_heckeTGeneratorGamma0_of_not_dvd hp hpN F hpm,
      show p * m = p ^ (0 + 1 - 2 * 0) * m by simp]
    simp
  · rw [qExpansion_coeff_prime_pow_succ_mul_heckeTGeneratorGamma0 hp hpN F m j,
      show min (j + 1) 1 + 1 = 2 by omega, Finset.sum_range_succ, Finset.sum_range_one,
      show j + 1 + 1 - 2 * 0 = j + 2 by omega, show j + 1 + 1 - 2 * 1 = j by omega]
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
    rw [heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_add_two hp hpN F r,
      qExpansion_coeff_coe_sub_smul]
    rcases j with _ | j
    · -- `p ∤ m`: the recurrence reads the coefficient at `p m`, which is the `j = 1` instance
      have h1 := ih1 0
      have h2 := ih2 1
      rw [pow_zero, one_mul] at h1
      rw [pow_one] at h2
      rw [pow_zero, one_mul, qExpansion_coeff_heckeTGeneratorGamma0_of_not_dvd hp hpN _ hpm, h2,
        h1]
      exact sum_range_min_zero
        (fun t ↦ (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (p ^ t * m))
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) r
    · -- both terms of the recurrence are present; the sums recombine by `sum_range_min_add_two`
      rw [qExpansion_coeff_prime_pow_succ_mul_heckeTGeneratorGamma0 hp hpN _ m j, ih2 (j + 2),
        ih2 j, ih1 (j + 1)]
      have h := sum_range_min_add_two
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
