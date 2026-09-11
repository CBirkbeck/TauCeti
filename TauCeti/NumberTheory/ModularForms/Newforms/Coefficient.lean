/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Composite
public import TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue

/-!
# The Fourier coefficients of a good Hecke eigenform are its eigenvalues

`Newforms/RingEigenvalue.lean` reads the eigenvalue system `λ` of an `EigenformAwayFromLevel` off
the multiplication table of the `Γ₀(N)` Hecke ring, touching no Fourier coefficient. This file
supplies the missing half: the composite Hecke element reads the coefficient at `m n` from the
coefficient at `m`, for `m` coprime to `n`
(`HeckeSlash/Nebentypus/Composite.lean`), so at `m = 1` the eigenvector equation becomes

`a_n(f) = λ_n · a_1(f)`   for every good index `n`,

and for a normalised newform, where `a_1 = 1`, simply `a_n(f) = λ_n`. That is the form in which
strong multiplicity one is classically stated — Miyake's Theorem 4.6.12 compares the `a_n`, not
the `λ_n` — and the identity that turns the eigenvalue identities of `RingEigenvalue.lean`
(`eigenvalue_mul`, `eigenvalue_prime_pow_add_two`) into the Fourier-coefficient conditions of
Diamond–Shurman's Proposition 5.8.5.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue_mul_coeff_one`:
  `a_n(f) = λ_n a_1(f)` at a good index.
* `HeckeRing.GL2.Newform.qExpansion_coeff_eq_eigenvalue`: `a_n(f) = λ_n` for a newform.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.8.5.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

namespace EigenformAwayFromLevel

variable (f : EigenformAwayFromLevel N k)

/-- **The coefficients of a good Hecke eigenform are its eigenvalues, scaled by `a₁`**:
`a_n(f) = λ_n a_1(f)` at every index `n` coprime to the level. The eigenvector equation at `n`,
read on the first coefficient: the Hecke element multiplies `a_1` by `λ_n` and reads `a_n`. -/
theorem qExpansion_coeff_eq_eigenvalue_mul_coeff_one (n : ℕ+) (hn : Nat.Coprime (n : ℕ) N) :
    (qExpansion 1 f.toCuspForm).coeff (n : ℕ) =
      f.eigenvalue n hn * (qExpansion 1 f.toCuspForm).coeff 1 := by
  have h := qExpansion_coeff_heckeTCompositeGamma0_of_coprime (N := N) (k := k) (χ := f.χ)
    n.pos.ne' hn ⟨f.toCuspForm, f.mem_charSpace⟩ (m := 1) (Nat.coprime_one_left _)
  rw [f.isEigen n hn, one_mul, Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _), map_smul,
    smul_eq_mul] at h
  exact h.symm

end EigenformAwayFromLevel

namespace Newform

variable (f : Newform N k)

/-- **The `q`-expansion coefficients of a newform are its eigenvalues**: `a_n(f) = λ_n` at every
index `n` coprime to the level, the normalisation `a_1 = 1` pinning the scalar. -/
theorem qExpansion_coeff_eq_eigenvalue (n : ℕ+) (hn : Nat.Coprime (n : ℕ) N) :
    (qExpansion 1 f.toCuspForm).coeff (n : ℕ) = f.eigenvalue n hn := by
  rw [f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue_mul_coeff_one n hn, f.isNorm,
    mul_one]

end Newform

end HeckeRing.GL2
