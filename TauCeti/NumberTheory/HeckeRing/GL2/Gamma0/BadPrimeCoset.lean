/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

-- `ZMod.coe_int_isUnit_iff_isCoprime`: the `Δ₀(N)` unit condition on the upper-left entry, read
-- as coprimality of an integer with the level.
public import Mathlib.Data.ZMod.Units
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DoubleCoset
public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

/-!
# The bad-prime double coset of `Δ₀(N)`

`Gamma0/DoubleCoset.lean` settles the **coprime** case: when `gcd(det α, N) = 1`, the
`SL₂(ℤ)`-double coset of `α` meets `Δ₀(N)` in exactly the `Γ₀(N)`-double coset. This file works
towards the complementary **bad-prime** case, Shimura Proposition 3.33: an element of `Δ₀(N)`
whose determinant `m` divides a power of `N` lies in the `Γ₀(N)`-double coset of `diag(1, m)`.

The proof is a column reduction. Coprimality of the upper-left entry to the determinant lets
one column operation clear the upper row modulo `m`; the determinant identity then forces the
lower-right entry to clear as well, leaving `A` in the left `Γ₀(N)`-coset of `!![1, r; 0, m]`
for a reduced `0 ≤ r < m`. Splitting that representative as `diag(1, m) · !![1, r; 0, 1]` moves
the remaining parameter into a second `Γ₀(N)` factor, which is what makes the conclusion a
*double* coset.

## Main results

* `HeckeRing.GL2.shimura_prop_3_33`: the proposition itself — an element of `Δ₀(N)` whose
  determinant `m` divides a power of the level lies in the `Γ₀(N)`-double coset of
  `diag(1, m)`.
* `HeckeRing.GL2.shimura_prop_3_33_gen`: the same conclusion drawn from an integral witness
  directly, with no `Δ₀(N)` hypothesis.
* `HeckeRing.GL2.Gamma0_left_coset_of_Npow_det`: the column reduction, stated on its own.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.33.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
  `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Props.lean`, declarations
  `exists_mod_clearing`, `dvd_lowerRight_witness`, `coprime_of_gcd_one_dvd_pow`,
  `shimura_prop_3_33_gen` and `shimura_prop_3_33`.

  Three source declarations are deliberately **not** ported. `diagMat_one_mem_Delta0` and
  `diagMat_mem_Delta0_of_gcd` are already on main as `natDiagGL_one_mem_Delta0` and
  `natDiagGL_mem_Delta0_of_coprime`. `fin2_col_scale` exists only to drive the source's
  entrywise `fin_cases`/`linarith` verification of the final matrix identity; that identity is
  established here by factoring `!![1, r; 0, m]` as `diag(1, m) · !![1, r; 0, 1]`
  (`shearMat_eq_diagonal_mul`) and pushing the cast through the product
  (`coe_mapGL_mul_natDiagGL_mul_mapGL`), so no per-entry lemma is needed.

  The source's `diagMat`/`Delta0_submonoid`/`(Gamma0_pair N).H` vocabulary is
  `natDiagGL`/`Delta0`/`(Gamma0 N).map (mapGL ℚ)` here, and the source's `[NeZero N]`
  instance and `β ∈ Δ₀(N)` hypothesis on the general form are both dropped as unused.
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

/-- **The reduced representative splits off its shear.** `!![1, r; 0, m]` is `diag(1, m)`
followed by the unipotent `!![1, r; 0, 1]`.

This one identity is what upgrades the column reduction from a *left*-coset statement to a
double-coset one. `Gamma0_left_coset_of_Npow_det` puts `A` in the left `Γ₀(N)`-coset of
`!![1, r; 0, m]`, which still mentions `r`; splitting the shear off on the right moves `r`
into a second `Γ₀(N)` factor, where it is harmless, a unipotent upper-triangular matrix
having lower-left entry `0` and so lying in `Γ₀(N)` for every level. -/
lemma shearMat_eq_diagonal_mul (m : ℕ) (r : ℤ) :
    (Matrix.of ![![(1 : ℤ), r], ![0, (m : ℤ)]]) =
      Matrix.diagonal (fun i ↦ ((![1, m] : Fin 2 → ℕ) i : ℤ)) *
        Matrix.of ![![(1 : ℤ), r], ![0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]

/-- **The `diag(1, m)` sandwich is the cast of an integral product.** Multiplying `diag(1, m)`
by the images of two integral special-linear matrices stays integral, and its matrix is the
cast of the corresponding product over `ℤ`.

Both `Γ₀(N)` factors of a double coset at `diag(1, m)` arrive as `mapGL ℚ` images, so this is
the bridge that lets the whole double-coset identity be checked over `ℤ`, where the column
reduction lives, instead of entrywise over `ℚ`. -/
lemma coe_mapGL_mul_natDiagGL_mul_mapGL (m : ℕ) (hm_pos : 0 < m) (g h : SL(2, ℤ)) :
    ((mapGL ℚ g * natDiagGL 2 ![1, m] * mapGL ℚ h : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ)
      = ((g : Matrix (Fin 2) (Fin 2) ℤ) *
          Matrix.diagonal (fun i ↦ ((![1, m] : Fin 2 → ℕ) i : ℤ)) *
          (h : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℚ) := by
  have hpos : ∀ i : Fin 2, 0 < (![1, m] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [hm_pos]
  -- `Matrix.map_mul` is stated for a bundled hom; `⇑(Int.castRingHom ℚ)` is definitionally the
  -- raw `Int.cast` the goal carries, so naming the instance once lets it rewrite there.
  have hmap (X Y : Matrix (Fin 2) (Fin 2) ℤ) :
      (X * Y).map (Int.cast : ℤ → ℚ) = X.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) :=
    Matrix.map_mul (f := Int.castRingHom ℚ)
  rw [Units.val_mul, Units.val_mul, hmap, hmap, mapGL_coe_matrix, mapGL_coe_matrix,
    natDiagGL_coe 2 _ hpos]
  simp [map_apply_coe, Matrix.diagonal_map]

/-- **Generalised Shimura 3.33.** An element of `GL₂(ℚ)` with an integral matrix `A` whose
lower-left entry is divisible by `N`, whose determinant is `m`, and whose upper-left entry is
coprime to `m`, lies in the `Γ₀(N)`-double coset of `diag(1, m)`.

Membership of `Δ₀(N)` is deliberately **not** assumed. The proof uses exactly the three facts
about `A` that `mem_Delta0_iff` would hand over, and the positivity of `det β` that comes with
`Δ₀(N)` membership plays no part; `shimura_prop_3_33` supplies the hypotheses from a genuine
`Δ₀(N)` element. -/
theorem shimura_prop_3_33_gen (N m : ℕ) (hm_pos : 0 < m) (β : GL (Fin 2) ℚ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (β : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hdet : (β : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ))
    (ham : Int.gcd (A 0 0) m = 1) :
    β ∈ DoubleCoset.doubleCoset (natDiagGL 2 ![1, m])
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨L, r, hL_det, hL_N, -, -, hA_eq⟩ :=
    Gamma0_left_coset_of_Npow_det N A hAN m hm_pos (intMat_det_of_coe β A hA m hdet) ham
  have hR_det : (Matrix.of ![![(1 : ℤ), r], ![0, 1]]).det = 1 := by
    simp [Matrix.det_fin_two]
  -- The two factors are named as `SL(2, ℤ)` *variables* rather than written as anonymous
  -- constructors. `SL(2, ℤ)` is reducibly the subtype `{A // A.det = 1}`, so an ascribed
  -- `(⟨L, hL_det⟩ : SL(2, ℤ))` elaborates to the subtype's constructor; the resulting goal is
  -- then ill-typed at `implicit` transparency and `mapGL_coe_matrix` cannot fire on it.
  obtain ⟨L_sl, hL_sl⟩ : ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) = L := ⟨⟨L, hL_det⟩, rfl⟩
  obtain ⟨R_sl, hR_sl⟩ : ∃ g : SL(2, ℤ),
      (g : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.of ![![(1 : ℤ), r], ![0, 1]] := ⟨⟨_, hR_det⟩, rfl⟩
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨mapGL ℚ L_sl, Subgroup.mem_map_of_mem _ (Gamma0_mem.mpr ?_),
    mapGL ℚ R_sl, Subgroup.mem_map_of_mem _ (Gamma0_mem.mpr ?_), Units.ext ?_⟩
  · exact hL_sl ▸ (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL_N
  · simp [hR_sl]
  · rw [coe_mapGL_mul_natDiagGL_mul_mapGL m hm_pos, hL_sl, hR_sl, hA, hA_eq,
      shearMat_eq_diagonal_mul, ← mul_assoc]

/-- **Shimura, Proposition 3.33.** An element of `Δ₀(N)` whose determinant `m` divides a power
of the level lies in the `Γ₀(N)`-double coset of `diag(1, m)`.

This is the bad-prime companion of `doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0_map`,
which settles the case `gcd(m, N) = 1`. Here the determinant is as far from coprime to the
level as it can be: every prime dividing `m` divides `N`. Together the two cover the
determinants a `Δ₀(N)` element can have at a prime power level. -/
theorem shimura_prop_3_33 (N m : ℕ) (hm_pos : 0 < m) (k : ℕ) (hm_dvd : m ∣ N ^ k)
    (β : GL (Fin 2) ℚ) (hβ : β ∈ Delta0 N)
    (hdet : (β : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) :
    β ∈ DoubleCoset.doubleCoset (natDiagGL 2 ![1, m])
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨A, hA, -, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hβ
  exact shimura_prop_3_33_gen N m hm_pos β A hA hAN hdet
    (coprime_of_gcd_one_dvd_pow (A 0 0) N m k
      (Int.isCoprime_iff_gcd_eq_one.mp
        (isCoprime_comm.mp ((ZMod.coe_int_isUnit_iff_isCoprime _ _).mp hAunit))) hm_dvd)

end HeckeRing.GL2

end
