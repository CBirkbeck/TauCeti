/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Recurrence
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# Eigen at the good primes is eigen at every good index

A cusp form of nebentypus `χ` that is an eigenvector of the `Γ₀(N)` Hecke ring at the generator
`T_p` of every prime `p ∤ N` is automatically an eigenvector at `heckeTCompositeGamma0 N n` for
*every* `n` coprime to `N`, and so carries a full eigenvalue system away from the level.

Nothing else in the library builds an `EigenformAwayFromLevel`: the structure is defined in
`Newforms/Newform.lean` and consumed downstream, but its `isEigen` field quantifies over all good
`n` while every route to eigen-ness — a coefficient recurrence, a diagonalisation, a spectral
argument — produces it one prime at a time. This file closes that gap.

The two facts doing the work are already on `main`: `heckeTCompositeGamma0_prime_pow` identifies
the composite at a prime power with the Diamond–Shurman recurrence family, and
`heckeTCompositeGamma0_mul_of_coprime` splits a general index into its prime powers. Since
`heckeRingHomCuspCharSpace` is a *ring* homomorphism, the elements acting on a fixed form by a
scalar are closed under products, which is what carries the eigen-property along both steps; the
recurrence contributes the third term `(p • S_p) · T_{p^r}`, whose scalar action is the nebentypus
(`heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_succ_succ`).

## Main results

* `HeckeRing.GL2.exists_smul_heckeTCompositeGamma0_of_forall_prime`: the eigen-property spreads
  from the good primes to every good index.
* `HeckeRing.GL2.EigenformAwayFromLevel.ofForallPrime`: the resulting good Hecke eigenform.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn

open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- A product of two Hecke-ring elements that each act on `F` by a scalar acts on `F` by a
scalar. This is the only closure property the spreading argument needs, and it holds because
`heckeRingHomCuspCharSpace` is a ring homomorphism. -/
private theorem exists_smul_mul {F : cuspFormCharSpace k χ}
    {x y : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ}
    (hx : ∃ c : ℂ, heckeRingHomCuspCharSpace k χ x F = c • F)
    (hy : ∃ c : ℂ, heckeRingHomCuspCharSpace k χ y F = c • F) :
    ∃ c : ℂ, heckeRingHomCuspCharSpace k χ (x * y) F = c • F := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a * b, by rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]⟩

/-- The eigen-property at the generator `T_p` of a good prime spreads along the recurrence family
to every `T_{p^v}`. The `r + 2` step is the Diamond–Shurman recurrence, whose scalar term acts
through the nebentypus. -/
private theorem exists_smul_heckeTGeneratorRecGamma0 {F : cuspFormCharSpace k χ} {p : ℕ}
    (hp : p.Prime) (hpN : Nat.Coprime p N)
    (h : ∃ c : ℂ, heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) F = c • F) (v : ℕ) :
    ∃ c : ℂ, heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p v) F = c • F := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    match v with
    | 0 => exact ⟨1, by rw [heckeTGeneratorRecGamma0_zero, map_one, Module.End.one_apply, one_smul]⟩
    | 1 => rwa [heckeTGeneratorRecGamma0_one]
    | (r + 2) =>
      obtain ⟨a, ha⟩ := ih (r + 1) (by omega)
      obtain ⟨b, hb⟩ := ih r (by omega)
      obtain ⟨c, hc⟩ := h
      refine ⟨c * a - (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) * b, ?_⟩
      rw [heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_succ_succ k χ hp.pos hpN r]
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, ha, hb,
        map_smul, hc, smul_smul, sub_smul]
      ring_nf

/-- **Eigen at every good prime is eigen at every good index.** If the Hecke-ring generator at
every prime `p ∤ N` acts on `F ∈ S_k(N, χ)` by a scalar, then so does `heckeTCompositeGamma0 N n`
for every `n ≠ 0` coprime to `N`.

The induction is `Nat.recOnPosPrimePosCoprime`: prime powers are the recurrence family, and a
coprime product is a product in the Hecke ring. -/
theorem exists_smul_heckeTCompositeGamma0_of_forall_prime {F : cuspFormCharSpace k χ}
    (h : ∀ p : ℕ, p.Prime → Nat.Coprime p N →
      ∃ c : ℂ, heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) F = c • F)
    (n : ℕ) (hn0 : n ≠ 0) (hnN : Nat.Coprime n N) :
    ∃ c : ℂ, heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) F = c • F := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p v hp hv =>
    have hpN : Nat.Coprime p N := hnN.coprime_dvd_left (dvd_pow_self p hv.ne')
    rw [heckeTCompositeGamma0_prime_pow N hp]
    exact exists_smul_heckeTGeneratorRecGamma0 hp hpN (h p hp hpN) v
  | zero => exact absurd rfl hn0
  | one => exact ⟨1, by rw [heckeTCompositeGamma0_one, map_one, Module.End.one_apply, one_smul]⟩
  | coprime a b ha hb hab iha ihb =>
    rw [heckeTCompositeGamma0_mul_of_coprime N hab]
    rw [Nat.coprime_mul_iff_left] at hnN
    exact exists_smul_mul (iha (by omega) hnN.1) (ihb (by omega) hnN.2)

namespace EigenformAwayFromLevel

/-- **A nonzero cusp form of nebentypus `χ`, eigen at every good prime, is a good Hecke
eigenform.** Its eigenvalue at a good index is the scalar produced by
`exists_smul_heckeTCompositeGamma0_of_forall_prime`. -/
noncomputable def ofForallPrime {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hχ : f ∈ cuspFormCharSpace k χ) (hf : f ≠ 0)
    (h : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨f, hχ⟩ = c • ⟨f, hχ⟩) :
    EigenformAwayFromLevel N k where
  toCuspForm := f
  χ := χ
  mem_charSpace := hχ
  eigenvalue n hn :=
    (exists_smul_heckeTCompositeGamma0_of_forall_prime h n n.ne_zero hn).choose
  isEigen n hn :=
    (exists_smul_heckeTCompositeGamma0_of_forall_prime h n n.ne_zero hn).choose_spec
  ne_zero := hf

end EigenformAwayFromLevel

end HeckeRing.GL2

end
