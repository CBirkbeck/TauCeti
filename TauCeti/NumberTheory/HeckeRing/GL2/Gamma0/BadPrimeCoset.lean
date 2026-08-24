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

end HeckeRing.GL2

end
