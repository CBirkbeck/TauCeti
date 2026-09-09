/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Cosets
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Invariance

/-!
# The level-descent matrices are permuted by `Γ₀(N / p)`

`Newforms/Descent/Cosets.lean` defines the family `descendMatrix p N` that Miyake's level
descent at a prime `p` runs over. This file proves the first of the two facts that file
explicitly leaves open: at a prime with `p² ∣ N`, right multiplication by an element of
`Γ₀(N / p)` permutes the family, up to left multiplication by an element of `Γ₀(N)`.

The permutation is named rather than left existential, because that is what the descent
consumes: a slash by `γ ∈ Γ₀(N / p)` sends the summand at `v` to the summand at
`descendShift p N hpsq γ v`, and the sum is unchanged only because that map is a bijection of
the index set.

## Why `p² ∣ N`

The hypothesis enters twice. It collapses `descendMatrixCount p N` to `p`, so every index is
that of an upper-triangular member; and it gives `p ∣ N / p`, which places `γ` in `Γ₀(p)`, and
that is what makes the offset map a bijection. When `p` exactly divides `N` there is one further
representative, `descendExtraGamma`, and the argument is different; that case is not proved here.

## Main definitions

* `TauCeti.descendShift`: `HeckeRing.GL2.upperTriShift` carried to `Fin (descendMatrixCount p N)`
  along `descendMatrixCount p N = p`.

## Main results

* `TauCeti.descendShift_bijective`: it is a bijection of the index set.
* `TauCeti.descendMatrix_mul_mapGL`: `descendMatrix p N v * γ = α * descendMatrix p N (shift v)`
  for some `α ∈ Γ₀(N)`.

## Scope

Only the `p² ∣ N` case, and only the factorisation together with the bijectivity of the shift.
The extra representative, the completeness of the family as a coset system, and the invariance
of the slash sum are separate statements and none of them is claimed here.

Corresponds to `descendCosetList_action_upper_tri_clean` of the AINTLIB `LeanModularForms`
project (`LeanModularForms/StrongMultiplicityOne/DescentCosets.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>). The proof is not
transcribed: the source builds the target index and the `Γ₀(N)` witness by hand from the matrix
entries, whereas here both come from `HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul`, which
already supplies them over `ℚ`, and mathlib's `Matrix.SpecialLinearGroup.map_mapGL` transports
the identity to `ℝ`.
-/

public section

open CongruenceSubgroup HeckeRing.GL2 Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace TauCeti

variable {p N : ℕ}

/-- **The offset map on the descent index set.** `HeckeRing.GL2.upperTriShift` carried across
`descendMatrixCount p N = p`, which holds because `p² ∣ N`. This is the map the descent's slash
sum reindexes along. -/
def descendShift (p N : ℕ) [NeZero p] (hpsq : p ^ 2 ∣ N) (γ : SL(2, ℤ))
    (v : Fin (descendMatrixCount p N)) : Fin (descendMatrixCount p N) :=
  (finCongr (descendMatrixCount_of_sq_dvd hpsq)).symm
    (upperTriShift p γ (finCongr (descendMatrixCount_of_sq_dvd hpsq) v))

/-- **The offset map is a bijection of the descent index set.** Transporting along an equivalence
preserves bijectivity, and `HeckeRing.GL2.upperTriShift_bijective` supplies it on `Fin p`; the
hypothesis is `γ ∈ Γ₀(p)`, which `p² ∣ N` gives for every `γ ∈ Γ₀(N / p)`. -/
theorem descendShift_bijective [NeZero p] (hpsq : p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγp : γ ∈ Gamma0 p) :
    Function.Bijective (descendShift p N hpsq γ) :=
  (finCongr (descendMatrixCount_of_sq_dvd (N := N) hpsq)).symm.bijective.comp
    ((upperTriShift_bijective hγp).comp
      (finCongr (descendMatrixCount_of_sq_dvd (N := N) hpsq)).bijective)

/-- **The descent family is permuted by `Γ₀(N / p)` when `p² ∣ N`.** For `γ ∈ Γ₀(N / p)`, the
product `descendMatrix p N v * γ` is an element of `Γ₀(N)` times the member of the family at
`descendShift p N hpsq γ v` — and that map is a bijection, by `descendShift_bijective`.

Naming the target index rather than hiding it behind an existential is what makes the statement
usable downstream: reindexing the descent's slash sum needs the permutation itself, not merely
the fact that some member of the family appears. -/
theorem descendMatrix_mul_mapGL (p N : ℕ) [NeZero p] (hpN : p ∣ N) (hpsq : p ^ 2 ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 (N / p)) (v : Fin (descendMatrixCount p N)) : ∃ α : SL(2, ℤ), α ∈ Gamma0 N ∧
      descendMatrix p N v * mapGL ℝ γ =
        mapGL ℝ α * descendMatrix p N (descendShift p N hpsq γ v) := by
  have hcount : descendMatrixCount p N = p := descendMatrixCount_of_sq_dvd hpsq
  have hv : v.val < p := lt_of_lt_of_le v.isLt hcount.le
  -- `p ∣ N / p` is exactly `p² ∣ N`, so `Γ₀(N / p) ≤ Γ₀(p)`
  have hpdvd : p ∣ N / p := (Nat.dvd_div_iff_mul_dvd hpN).mpr (by rwa [← sq])
  -- the second hypothesis is `N ∣ p c`, from `(N / p) ∣ c` and `p · (N / p) = N`
  have hpc : (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
    have hpNp : (N : ℤ) = (p : ℤ) * ((N / p : ℕ) : ℤ) := by
      exact_mod_cast (Nat.mul_div_cancel' hpN).symm
    rw [hpNp]
    exact mul_dvd_mul_left _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))
  obtain ⟨α, hα, _, hmul⟩ :=
    exists_mem_Gamma0_upperTriRep_mul (Gamma0_le_Gamma0_of_dvd hpdvd hγ) hpc ⟨v.val, hv⟩
  have hv' : ((descendShift p N hpsq γ v : Fin (descendMatrixCount p N)) : ℕ) < p :=
    lt_of_lt_of_le (descendShift p N hpsq γ v).isLt hcount.le
  refine ⟨α, hα, ?_⟩
  rw [descendMatrix_of_lt hv, descendMatrix_of_lt hv', ← map_mapGL (S := ℚ) (T := ℝ) γ,
    ← map_mapGL (S := ℚ) (T := ℝ) α, ← map_mul, ← map_mul]
  exact congrArg _ hmul

end TauCeti
