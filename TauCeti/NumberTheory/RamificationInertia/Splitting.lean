/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Complete splitting forces trivial ramification and inertia

This file records the non-Galois half of the counting criterion for primes in finite flat
extensions of domains: if a prime has as many primes above it as the degree allows, then every
one of them is unramified with trivial residue extension.

The Galois form, where the count is compared with the order of the Galois group, is in
`TauCeti/NumberTheory/RamificationInertia/Galois.lean`. No Galois hypothesis is needed here:
the fundamental identity alone forces each summand `e * f` down to `1`.

## Main results

In the `TauCeti.RamificationInertia` namespace:

* `ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank` — a maximal count
  of primes above `P` makes `e = f = 1` at each of them.

## Provenance

Built directly on Mathlib's fundamental identity for finite flat extensions of domains
(`Ideal.sum_ramification_inertia_eq_finrank`).
-/

public section

open Ideal Module

namespace TauCeti.RamificationInertia

/-- **A maximal count of primes above `P` forces `e = f = 1`.** If the number of primes of `S`
lying over a prime `P` of `R` equals the rank of `S` over `R`, then each such prime is unramified
over `P` and has trivial inertia degree. No Galois hypothesis is needed. -/
theorem ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Module.Flat R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S)
    [Q.IsPrime] [Q.LiesOver P] (hsplit : (P.primesOver S).ncard = finrank R S) :
    Q.ramificationIdx R = 1 ∧ Q.inertiaDeg R = 1 := by
  have hfin : Fintype (P.primesOver S) := (Algebra.QuasiFinite.finite_primesOver P).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (R := R) (S := S) (p := P)
  have hcard : Fintype.card (P.primesOver S) = finrank R S := by
    rw [← hsplit, Set.ncard_eq_toFinset_card']
    simp
  -- the fundamental identity writes the rank as `∑ e * f` over the primes above `P`; each
  -- summand is at least `1`, and their number already accounts for the whole rank
  have hone : ∀ q ∈ (Finset.univ : Finset (P.primesOver S)),
      1 ≤ q.1.ramificationIdx R * q.1.inertiaDeg R := fun q _ =>
    Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Ideal.ramificationIdx_pos (R := R) (q := q.1)).ne'
        (Ideal.inertiaDeg_pos (R := R) (q := q.1)).ne')
  have hEqSum : ∑ _q : P.primesOver S, (1 : ℕ) =
      ∑ q : P.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R := by
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard]
  have hQ : (⟨Q, ⟨inferInstance, inferInstance⟩⟩ : P.primesOver S) ∈ Finset.univ :=
    Finset.mem_univ _
  have := (Finset.sum_eq_sum_iff_of_le hone).mp hEqSum _ hQ
  exact ⟨Nat.eq_one_of_mul_eq_one_right this.symm, Nat.eq_one_of_mul_eq_one_left this.symm⟩

end TauCeti.RamificationInertia
