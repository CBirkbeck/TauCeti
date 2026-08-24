/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DoubleCoset
public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

/-!
# The bad-prime double coset of `Δ₀(N)`

`Gamma0/DoubleCoset.lean` settles the **coprime** case: when `gcd(det α, N) = 1`, the
`SL₂(ℤ)`-double coset of `α` meets `Δ₀(N)` in exactly the `Γ₀(N)`-double coset. This file works
towards the complementary **bad-prime** case, Shimura Proposition 3.33: an element of `Δ₀(N)`
whose determinant `m` divides a power of `N` lies in the `Γ₀(N)`-double coset of `diag(1, m)`.

Only the arithmetic prelude is here so far. The clearing lemmas below are what turn a `Δ₀(N)`
representative into one with the lower-left entry cleared, which is the step the coset
identification runs on.

## Main results

* `HeckeRing.GL2.exists_mod_clearing`: Bézout in the form the row operation needs — if
  `gcd(a, p) = 1` then some `t` makes `p ∣ t * a + c`.
* `HeckeRing.GL2.dvd_lowerRight_witness`: with the determinant fixed and the upper-left entry
  coprime to it, clearing the upper row also clears the lower-right entry modulo `m`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.33.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
  `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Props.lean`, declarations
  `exists_mod_clearing`, `dvd_lowerRight_witness`, `fin2_col_scale` and
  `coprime_of_gcd_one_dvd_pow`. The source's `diagMat`/`Delta0_submonoid` vocabulary is
  `natDiagGL`/`Delta0` here, and its `diagMat_one_mem_Delta0` and `diagMat_mem_Delta0_of_gcd`
  are **not** re-ported: they are already on main as `natDiagGL_one_mem_Delta0` and
  `natDiagGL_mem_Delta0_of_coprime`.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn

open scoped MatrixGroups

namespace HeckeRing.GL2

/-- **Bézout, in the shape a row operation needs.** If `a` is coprime to `p` then the residue
of `c` can be cleared by adding a multiple of `a`: some `t` has `p ∣ t * a + c`.

Stated over `ℤ` with `p : ℕ` because the modulus arrives as a natural determinant. -/
lemma exists_mod_clearing (a c : ℤ) (p : ℕ) (hap : Int.gcd a p = 1) :
    ∃ t : ℤ, (p : ℤ) ∣ (t * a + c) := by
  refine ⟨-c * Int.gcdA a p, ⟨c * Int.gcdB a p, ?_⟩⟩
  have bez := Int.gcd_eq_gcd_ab a p
  rw [hap] at bez
  linear_combination c * bez

/-- **Clearing the upper row clears the lower-right entry too.** For an integral matrix whose
lower-left entry is `N * c₀` and whose determinant is `m`, with the upper-left entry coprime to
`m`: if `m` divides `A 0 0 * r - A 0 1` then it divides `A 1 1 - N * c₀ * r`.

This is the bookkeeping that lets one column operation put a `Δ₀(N)` representative into the
shape `diag(1, m)` sits in. The determinant identity does the work; coprimality of `A 0 0` with
`m` is what lets it be cancelled. -/
lemma dvd_lowerRight_witness (A : Matrix (Fin 2) (Fin 2) ℤ) (N m : ℕ) (c₀ r : ℤ)
    (hc₀ : A 1 0 = (N : ℤ) * c₀) (hdet : A.det = m) (ham : Int.gcd (A 0 0) m = 1)
    (hm_ar_b : (m : ℤ) ∣ (A 0 0 * r - A 0 1)) :
    (m : ℤ) ∣ (A 1 1 - (N : ℤ) * c₀ * r) := by
  have h_key : A 0 0 * (A 1 1 - (N : ℤ) * c₀ * r)
      = (m : ℤ) + (A 0 1 - A 0 0 * r) * ((N : ℤ) * c₀) := by
    have h_det := Matrix.det_fin_two A
    rw [hc₀, hdet] at h_det
    linarith
  have hm_ba : (m : ℤ) ∣ (A 0 1 - A 0 0 * r) := by
    obtain ⟨w, hw⟩ := hm_ar_b
    exact ⟨-w, by linarith⟩
  exact ((Int.isCoprime_iff_gcd_eq_one.mpr ham).symm).dvd_of_dvd_mul_left
    (h_key ▸ dvd_add (dvd_refl _) (dvd_mul_of_dvd_left hm_ba _))

/-- The second column of `diag(1, m)` is `m` times the second standard basis vector. -/
lemma fin2_col_scale (m : ℕ) (j : Fin 2) :
    (![0, (m : ℤ)] : Fin 2 → ℤ) j = (m : ℤ) * (![0, 1] : Fin 2 → ℤ) j := by
  fin_cases j <;> simp

/-- Coprimality passes to a divisor of a power: if `a` is coprime to `N` and `k ∣ N ^ e`, then
`a` is coprime to `k`. This is what carries the `Δ₀(N)` coprimality hypothesis down to the
determinant in the bad-prime case, where the determinant divides a power of the level. -/
lemma coprime_of_gcd_one_dvd_pow (a : ℤ) (N k e : ℕ) (haN : Int.gcd a N = 1)
    (hk_dvd : k ∣ N ^ e) : Int.gcd a k = 1 :=
  Nat.Coprime.coprime_dvd_right hk_dvd (Nat.Coprime.pow_right e haN)

/-- **The reduced shear parameter.** With `A 0 0` coprime to `m` there is an `r` in `[0, m)`
clearing the upper row modulo `m`: `m ∣ A 0 0 * r - A 0 1`.

Split out of `Gamma0_left_coset_of_Npow_det` below: it is the arithmetic half, and isolating
it keeps that lemma's matrix bookkeeping readable. -/
lemma exists_reduced_shear (A : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (hm_pos : 0 < m)
    (ham : Int.gcd (A 0 0) m = 1) :
    ∃ r : ℤ, 0 ≤ r ∧ r < m ∧ (m : ℤ) ∣ (A 0 0 * r - A 0 1) := by
  obtain ⟨t_inv, ht⟩ := exists_mod_clearing (A 0 0) (-A 0 1) m ham
  refine ⟨t_inv % (m : ℤ), Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega), ?_⟩
  have hm_tr : (m : ℤ) ∣ (t_inv - t_inv % (m : ℤ)) := by
    rw [show t_inv - t_inv % (m : ℤ) = (m : ℤ) * (t_inv / (m : ℤ)) by
      linarith [Int.mul_ediv_add_emod t_inv ((m : ℤ))]]
    exact dvd_mul_right _ _
  have h := dvd_sub ht (dvd_mul_of_dvd_left hm_tr (A 0 0))
  rwa [show t_inv * A 0 0 + -A 0 1 - (t_inv - t_inv % (m : ℤ)) * A 0 0
      = A 0 0 * (t_inv % (m : ℤ)) - A 0 1 by ring] at h

/-- **The determinant of an integral witness.** If `A` represents `g ∈ GL₂(ℚ)` entrywise over
`ℤ` and `g` has determinant `m`, then `A` has determinant `m` over `ℤ`.

The `Δ₀(N)` membership predicate states positivity of the determinant on the `ℚ`-side while the
column reduction works on the `ℤ`-side, so this cast bridge is needed to move between them.
AINTLIB has it as `det_intMat_cast`; TauCeti has no equivalent, so it is stated here from
Mathlib's `RingHom.map_det`. -/
lemma intMat_det_of_coe (g : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) (m : ℕ)
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) :
    A.det = (m : ℤ) := by
  have h : ((A.det : ℤ) : ℚ) = (m : ℚ) := by
    rw [← hdet, hA, Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [Matrix.map_apply]
    push_cast
    ring
  exact_mod_cast h

/-- **The cofactor pair is unimodular.** Given the two divisibility witnesses `q₁, q₂` produced
by the column reduction, the matrix `!![A 0 0, -q₁; N * c₀, q₂]` has determinant one.

The identity holds after multiplying by `m` — that is just `det A = m` rearranged — and `m ≠ 0`
cancels it. Split out of `Gamma0_left_coset_of_Npow_det` to keep that proof under the
decomposition threshold. -/
lemma cofactor_pair_unimodular (A : Matrix (Fin 2) (Fin 2) ℤ) (N m : ℕ) (hm_pos : 0 < m)
    (c₀ r q₁ q₂ : ℤ) (hc₀ : A 1 0 = (N : ℤ) * c₀) (hdet : A.det = m)
    (hq₁ : A 0 0 * r - A 0 1 = (m : ℤ) * q₁)
    (hq₂ : A 1 1 - (N : ℤ) * c₀ * r = (m : ℤ) * q₂) :
    A 0 0 * q₂ + q₁ * ((N : ℤ) * c₀) = 1 := by
  have hdet' : A 0 0 * A 1 1 - A 0 1 * ((N : ℤ) * c₀) = (m : ℤ) := by
    rw [← hdet, Matrix.det_fin_two, hc₀]
  have h1 : (A 0 0 * q₂ + q₁ * ((N : ℤ) * c₀)) * (m : ℤ) = 1 * (m : ℤ) := by
    rw [one_mul]
    calc (A 0 0 * q₂ + q₁ * ((N : ℤ) * c₀)) * (m : ℤ)
        = A 0 0 * ((m : ℤ) * q₂) + ((m : ℤ) * q₁) * ((N : ℤ) * c₀) := by ring
      _ = A 0 0 * (A 1 1 - (N : ℤ) * c₀ * r) + (A 0 0 * r - A 0 1) * ((N : ℤ) * c₀) := by
            rw [← hq₂, ← hq₁]
      _ = (m : ℤ) := by linarith [hdet']
  exact mul_right_cancel₀ (show ((m : ℤ)) ≠ 0 by omega) h1

/-- **The left-coset normal form at a bad determinant.** An integral matrix with lower-left
entry divisible by `N`, determinant `m`, and upper-left entry coprime to `m`, factors as
`L * !![1, r; 0, m]` with `L` again of that `Γ₀`-shape — determinant one and lower-left entry
divisible by `N` — and `r` reduced into `[0, m)`.

This is the column reduction behind Shimura 3.33: it exhibits `A` in the left `Γ₀(N)`-coset of
the upper-triangular representative `!![1, r; 0, m]`. Positivity of `det A` is *not* needed —
the source carries it and never uses it. -/
lemma Gamma0_left_coset_of_Npow_det (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hAN : (N : ℤ) ∣ A 1 0) (m : ℕ) (hm_pos : 0 < m) (hdet : A.det = m)
    (ham : Int.gcd (A 0 0) m = 1) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℤ) (r : ℤ), L.det = 1 ∧ (N : ℤ) ∣ L 1 0 ∧ 0 ≤ r ∧ r < m ∧
      A = L * (Matrix.of ![![(1 : ℤ), r], ![0, (m : ℤ)]]) := by
  obtain ⟨c₀, hc₀⟩ := hAN
  obtain ⟨r, hr_nonneg, hr_lt, hm_ar_b⟩ := exists_reduced_shear A m hm_pos ham
  obtain ⟨q₂, hq₂⟩ := dvd_lowerRight_witness A N m c₀ r hc₀ hdet ham hm_ar_b
  obtain ⟨q₁, hq₁⟩ := hm_ar_b
  refine ⟨Matrix.of ![![A 0 0, -q₁], ![(N : ℤ) * c₀, q₂]], r, ?_, ?_, hr_nonneg, hr_lt, ?_⟩
  · simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val']
    linarith [cofactor_pair_unimodular A N m hm_pos c₀ r q₁ q₂ hc₀ hdet hq₁ hq₂]
  · norm_num [Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val',
      Matrix.cons_val_zero]
  · have h00 : A 0 0 = A 0 0 * 1 + (-q₁) * 0 := by ring
    have h01 : A 0 1 = A 0 0 * r + (-q₁) * (m : ℤ) := by linarith [hq₁]
    have h10 : A 1 0 = (N : ℤ) * c₀ * 1 + q₂ * 0 := by linarith [hc₀]
    have h11 : A 1 1 = (N : ℤ) * c₀ * r + q₂ * (m : ℤ) := by linarith [hq₂]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val'] <;>
      first | exact h00 | exact h01 | exact h10 | exact h11

end HeckeRing.GL2

end
