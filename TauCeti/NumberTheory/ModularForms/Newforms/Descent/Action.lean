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
`Γ₀(N / p)` carries each member of the family back into the family, up to left multiplication
by an element of `Γ₀(N)`.

That is what makes the family a *set of coset representatives* rather than merely a list of
determinant-`p` matrices, and it is the step the slash sum needs: a slash by `γ' ∈ Γ₀(N / p)`
permutes the summands and so leaves the sum invariant.

## Why `p² ∣ N`

The descent splits on whether `p` divides `N` exactly. When `p² ∣ N` the family is the `p`
upper-triangular matrices `[1, v; 0, p]` and nothing else, and the permutation is the offset map
`HeckeRing.GL2.upperTriShift` already available at the level of `Γ₀(p)`. When `p ∤ (N / p)` there
is one further representative, `descendExtraGamma`, and the argument is different; that case is
not proved here.

## Main results

* `TauCeti.exists_mem_Gamma0_descendMatrix_mul`: for `p² ∣ N` and `γ ∈ Γ₀(N / p)`, each
  `descendMatrix p N v` times `γ` is an element of `Γ₀(N)` times another member of the family.

## Scope

Only the `p² ∣ N` case is proved, and only the factorisation itself. The extra representative,
the completeness of the family as a coset system, and the invariance of the slash sum are all
separate statements and none of them is claimed here.

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

open CongruenceSubgroup HeckeRing.GL2 Matrix

open scoped MatrixGroups

namespace TauCeti

/-- **The descent family is permuted by `Γ₀(N / p)` when `p² ∣ N`.** For `γ ∈ Γ₀(N / p)`, each
member `descendMatrix p N v` satisfies `descendMatrix p N v * γ = α * descendMatrix p N v'` for
some `α ∈ Γ₀(N)` and some further member `descendMatrix p N v'`.

The index `v'` is not arbitrary: it is the offset `HeckeRing.GL2.upperTriShift p γ v`, the unique
solution of `a v' ≡ b + v d (mod p)`, which `HeckeRing.GL2.upperTriShift_bijective` shows is a
permutation of the index set. This statement records only the existence of the factorisation;
that the map `v ↦ v'` is that permutation is read off `upperTriShift` directly at the call site.

`p² ∣ N` enters twice: it collapses `descendMatrixCount p N` to `p`, so every index is that of an
upper-triangular member, and it gives `p ∣ N / p`, so `Γ₀(N / p) ≤ Γ₀(p)` and the offset map is
available. -/
theorem exists_mem_Gamma0_descendMatrix_mul (p N : ℕ) [NeZero p] [NeZero N] (hpN : p ∣ N)
    (hpsq : p ^ 2 ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / p))
    (v : Fin (descendMatrixCount p N)) :
    ∃ (v' : Fin (descendMatrixCount p N)) (α : SL(2, ℤ)), α ∈ Gamma0 N ∧
      descendMatrix p N v * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ α * descendMatrix p N v' := by
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
  set j' := upperTriShift p γ ⟨v.val, hv⟩ with hj'
  have hlt : j'.val < descendMatrixCount p N := lt_of_lt_of_le j'.isLt hcount.ge
  refine ⟨⟨j'.val, hlt⟩, α, hα, ?_⟩
  have hv' : ((⟨j'.val, hlt⟩ : Fin (descendMatrixCount p N)) : ℕ) < p := j'.isLt
  rw [descendMatrix_of_lt hv, descendMatrix_of_lt hv',
    ← Matrix.SpecialLinearGroup.map_mapGL (S := ℚ) (T := ℝ) γ,
    ← Matrix.SpecialLinearGroup.map_mapGL (S := ℚ) (T := ℝ) α, ← map_mul, ← map_mul]
  exact congrArg _ hmul

end TauCeti
