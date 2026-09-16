/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import TauCeti.RingTheory.DedekindDomain.Discriminant.Basic

/-!
# Coefficients of the relative discriminant

The relative discriminant `relDiscr A B` is the relative norm of the different ideal, so its
coefficient at a nonzero maximal ideal `p` of `A` is determined by the coefficients of the
different at the primes of `B` above `p`, each weighted by a residue degree:

`mult_p(relDiscr A B) = Σ_{P ∣ p} f(P / p) · mult_P(𝔇(B / A))`.

The weights come from `Ideal.relNorm P = p ^ f(P / p)` for a maximal `P` above `p`. Both sides
are additive in the ideal being normed, so the formula is proved for an arbitrary nonzero ideal
first, by induction on its factorization, and then specialized to the different.

The coefficient `mult_p(I)` is Mathlib's `multiplicity`, the normalization in which
`Ideal.finprod_heightOneSpectrum_pow_multiplicity` recovers an ideal from its coefficients.

## Main results

* `TauCeti.multiplicity_relNorm`: the coefficient of a relative norm at `p` is the weighted sum
  of the coefficients of the ideal at the primes above `p`.
* `TauCeti.multiplicity_relDiscr`: the same formula for the relative discriminant, whose
  coefficients are those of the different.

## References

* [J. Neukirch, *Algebraic number theory*][neukirch1999], Chapter III, §2.
-/

public section

open Ideal UniqueFactorizationMonoid

namespace TauCeti

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [PerfectField (FractionRing A)]

section Prime

/-- Distinct primes of `B` do not divide one another, so the coefficient of `Q` at `P` vanishes
unless the two agree. -/
private theorem multiplicity_eq_zero_of_ne {P Q : Ideal B} (hP0 : P ≠ ⊥) [P.IsPrime]
    [Q.IsPrime] (hne : Q ≠ P) : multiplicity Q P = 0 := by
  refine multiplicity_eq_zero.mpr fun hdvd => hne ?_
  -- `Q ∣ P` means `P ≤ Q`; `P` is maximal and `Q ≠ ⊤`, so the two agree.
  exact (Ideal.IsMaximal.eq_of_le (‹P.IsPrime›.isMaximal hP0) (Ideal.IsPrime.ne_top ‹Q.IsPrime›)
    (Ideal.dvd_iff_le.mp hdvd)).symm

/-- The coefficient of `relNorm A P` at a nonzero maximal ideal `p` below `P` is the residue
degree of `P` over `p`, because the relative norm of `P` is `p ^ f(P / p)`. -/
private theorem multiplicity_relNorm_of_liesOver (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p] :
    multiplicity p (relNorm A P) = P.inertiaDeg A := by
  rw [Ideal.relNorm_eq_pow_of_isMaximal P p]
  exact multiplicity_pow_self_of_prime (Ideal.prime_of_isPrime hp inferInstance) _

/-- A prime of `B` not lying over `p` contributes nothing at `p`: its relative norm is a power
of a maximal ideal different from `p`. -/
private theorem multiplicity_relNorm_of_not_liesOver (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] (h : ¬ P.LiesOver p) :
    multiplicity p (relNorm A P) = 0 := by
  have hpp : Prime p := Ideal.prime_of_isPrime hp inferInstance
  have hne : P.under A ≠ p := fun hEq => h ⟨hEq.symm⟩
  rw [Ideal.relNorm_eq_pow_of_isMaximal P (P.under A)]
  -- `p` is prime, so dividing a power of `P.under A` forces `p = P.under A`.
  refine multiplicity_eq_zero.mpr fun hdvd => hne ?_
  have hle : P.under A ≤ p := Ideal.dvd_iff_le.mp (hpp.dvd_of_dvd_pow hdvd)
  exact (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) hle)

/-- **The coefficients of the relative norm of a prime.** Only the prime itself contributes, and
only when it lies over `p`, where it contributes its residue degree. -/
private theorem multiplicity_relNorm_prime (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) (hP0 : P ≠ ⊥) [P.IsPrime] :
    multiplicity p (relNorm A P) =
      ∑ Q ∈ (p.primesOver B).toFinset, Q.inertiaDeg A * multiplicity Q P := by
  classical
  have hPmax : P.IsMaximal := ‹P.IsPrime›.isMaximal hP0
  by_cases hlies : P.LiesOver p
  · have hmem : P ∈ (p.primesOver B).toFinset := Set.mem_toFinset.mpr ⟨‹P.IsPrime›, hlies⟩
    rw [Finset.sum_eq_single P (fun Q hQ hQP => ?_) (fun hP => absurd hmem hP)]
    · rw [multiplicity_self, Nat.mul_one, multiplicity_relNorm_of_liesOver p hp P]
    · have hQ' := Set.mem_toFinset.mp hQ
      have : Q.IsPrime := hQ'.1
      rw [multiplicity_eq_zero_of_ne hP0 hQP, Nat.mul_zero]
  · rw [multiplicity_relNorm_of_not_liesOver p hp P hlies]
    refine (Finset.sum_eq_zero fun Q hQ => ?_).symm
    have hQ' := Set.mem_toFinset.mp hQ
    have : Q.IsPrime := hQ'.1
    have : Q.LiesOver p := hQ'.2
    have hQP : Q ≠ P := fun hEq => hlies (hEq ▸ ‹Q.LiesOver p›)
    rw [multiplicity_eq_zero_of_ne hP0 hQP, Nat.mul_zero]

end Prime

variable (B) in
/-- **The coefficients of a relative norm.** For a nonzero ideal `I` of `B` and a nonzero
maximal ideal `p` of `A`, the coefficient of `relNorm A I` at `p` is the sum, over the primes
`P` of `B` above `p`, of the coefficient of `I` at `P` weighted by the residue degree of `P`
over `p`. -/
theorem multiplicity_relNorm (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) {I : Ideal B}
    (hI : I ≠ ⊥) :
    multiplicity p (relNorm A I) =
      ∑ P ∈ (p.primesOver B).toFinset, P.inertiaDeg A * multiplicity P I := by
  classical
  have hpp : Prime p := Ideal.prime_of_isPrime hp inferInstance
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx =>
    -- A unit ideal is `⊤`, which no prime divides, so both sides vanish.
    have hx' : x = ⊤ := Ideal.isUnit_iff.mp hx
    subst hx'
    have hptop : multiplicity p (⊤ : Ideal A) = 0 :=
      multiplicity_eq_zero.mpr fun hdvd =>
        (Ideal.IsPrime.ne_top inferInstance) (top_le_iff.mp (Ideal.dvd_iff_le.mp hdvd))
    rw [Ideal.relNorm_top, hptop]
    refine (Finset.sum_eq_zero fun Q hQ => ?_).symm
    have hQp : Q.IsPrime := (Set.mem_toFinset.mp hQ).1
    have hQtop : multiplicity Q (⊤ : Ideal B) = 0 :=
      multiplicity_eq_zero.mpr fun hdvd =>
        hQp.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hdvd))
    rw [hQtop, Nat.mul_zero]
  | h₃ J P hJ hP ih =>
    -- The `≠ ⊥` guard is part of the motive, so it is already introduced here.
    have hJ' : J ≠ ⊥ := hJ
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have hPprime : P.IsPrime := Ideal.isPrime_of_prime hP
    have hnb : relNorm A P * relNorm A J ≠ ⊥ :=
      mul_ne_zero (fun h => hP0 (Ideal.relNorm_eq_bot_iff.mp h))
        (fun h => hJ (Ideal.relNorm_eq_bot_iff.mp h))
    rw [map_mul, multiplicity_mul hpp (FiniteMultiplicity.of_prime_left hpp hnb),
      multiplicity_relNorm_prime p hp P hP0, ih hJ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    have hQp : Q.IsPrime := (Set.mem_toFinset.mp hQ).1
    have hQl : Q.LiesOver p := (Set.mem_toFinset.mp hQ).2
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp Q
    rw [multiplicity_mul (Ideal.prime_of_isPrime hQ0 hQp)
      (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hQ0 hQp)
        (mul_ne_zero hP0 hJ)), Nat.mul_add]

variable (B) in
/-- **The coefficients of the relative discriminant.** At a nonzero maximal ideal `p` of `A`,
the coefficient of `relDiscr A B` is the sum of the coefficients of the different at the primes
above `p`, each weighted by its residue degree. -/
theorem multiplicity_relDiscr (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (hd : differentIdeal A B ≠ ⊥) :
    multiplicity p (relDiscr A B) =
      ∑ P ∈ (p.primesOver B).toFinset,
        P.inertiaDeg A * multiplicity P (differentIdeal A B) := by
  rw [relDiscr_def]
  exact multiplicity_relNorm B p hp hd

end TauCeti

end
