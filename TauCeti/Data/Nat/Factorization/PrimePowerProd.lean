/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Pow
public import Mathlib.Data.Nat.PrimeFin

/-!
# Ordered products over a prime factorisation

`n.factorization.prod f` multiplies the blocks `f p (n.factorization p)` over the primes
dividing `n`. Being a `Finsupp.prod` it asks for a `CommMonoid`: a `Finsupp` records no order
on its support, so the product is only well defined once the factors commute.

`TauCeti.Nat.primePowerProd f n` multiplies the same blocks in a fixed order — least prime
first — and so asks only for a `MulOneClass`. Each step peels `Nat.minFac n` together with its
whole multiplicity, and recurses on `ordCompl[n.minFac] n`. Both `n = 0` and `n = 1` give the
empty product.

The ordering is not the point; the weakened typeclass is. A monoid that happens to be
commutative without carrying a `CommMonoid` *instance* — a Hecke ring whose commutativity is a
theorem rather than a structure field, say — cannot form `n.factorization.prod f` at all, and
this is what it forms instead. `primePowerProd_eq_factorization_prod` records that nothing is
lost: as soon as a `CommMonoid` instance is available the two agree.

Associativity is never used either — the bracketing is fixed, and `mul_one` is the only unit
law the proofs call on — so the first section below asks `MulOneClass` rather than `Monoid`,
in the same spirit as `List.prod`, which Lean defines at `Mul` plus `One`. Only the
`Finsupp.prod` comparison and the coprime multiplicativity that follows from it need the full
`CommMonoid`.

## Main definitions

* `TauCeti.Nat.primePowerProd`: the product of `f p (n.factorization p)` over the primes of
  `n`, taken in increasing order of prime.

## Main results

* `TauCeti.Nat.primePowerProd_of_one_lt`: the peeling step, as a rewriting rule.
* `TauCeti.Nat.primePowerProd_prime_pow`: on a prime power the product is a single block.
* `TauCeti.Nat.primePowerProd_eq_factorization_prod`: in a `CommMonoid` it is
  `n.factorization.prod f`.
* `TauCeti.Nat.primePowerProd_mul_of_coprime`: multiplicativity on coprime arguments.
-/

public section

namespace TauCeti

namespace Nat

variable {M : Type*}

section MulOneClass

variable [MulOneClass M]

/-- The product of the blocks `f p (n.factorization p)` over the primes `p` dividing `n`, taken
in increasing order of `p`: each step peels off the least prime factor of `n` together with its
whole multiplicity. The empty product `1` is returned at `n = 1`, and at `n = 0` as a junk
value — `0` has no factorisation to run over.

Only `MulOneClass M` is asked, which is the whole point of the definition; see
`primePowerProd_eq_factorization_prod` for the agreement with `n.factorization.prod f` when `M`
is commutative. -/
noncomputable def primePowerProd (f : ℕ → ℕ → M) (n : ℕ) : M :=
  if _h : n ≤ 1 then 1
  else
    f n.minFac (n.factorization n.minFac) *
      primePowerProd f (n / n.minFac ^ n.factorization n.minFac)
termination_by n
decreasing_by
  have hp : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
  exact Nat.div_lt_self (by omega)
    (Nat.one_lt_pow (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd n)).ne' hp.one_lt)

@[simp]
theorem primePowerProd_zero (f : ℕ → ℕ → M) : primePowerProd f 0 = 1 := by
  rw [primePowerProd]; simp

@[simp]
theorem primePowerProd_one (f : ℕ → ℕ → M) : primePowerProd f 1 = 1 := by
  rw [primePowerProd]; simp

/-- **The peeling step**: for `1 < n` the product splits off the block at `n.minFac`. This is
the only route to the body, which is sealed, and it is the equation every induction below
runs on. -/
theorem primePowerProd_of_one_lt (f : ℕ → ℕ → M) {n : ℕ} (hn : 1 < n) : primePowerProd f n =
    f n.minFac (n.factorization n.minFac) *
      primePowerProd f (n / n.minFac ^ n.factorization n.minFac) := by
  rw [primePowerProd, dite_eq_right (by omega : ¬n ≤ 1)]

/-- On a prime power the product is a single block: `primePowerProd f (p ^ v) = f p v`. The
hypothesis `v ≠ 0` is needed — at `v = 0` the left-hand side is the empty product `1` while the
right-hand side is `f p 0`, and nothing forces those to agree. -/
theorem primePowerProd_prime_pow (f : ℕ → ℕ → M) {p : ℕ} (hp : p.Prime) {v : ℕ} (hv : v ≠ 0) :
    primePowerProd f (p ^ v) = f p v := by
  rw [primePowerProd_of_one_lt f (Nat.one_lt_pow hv hp.one_lt), hp.pow_minFac hv,
    Nat.factorization_pow_self hp, Nat.div_self (pow_pos hp.pos v), primePowerProd_one, mul_one]

end MulOneClass

section CommMonoid

variable [CommMonoid M]

/-- Once the factors commute the ordering is invisible and the ordered product is the
`Finsupp.prod` over the factorisation. Stated for `n ≠ 0`: at `n = 0` the left-hand side is the
junk value `1` while `Nat.factorization 0 = 0`, so the right-hand side is `1` as well — but for
the trivial reason, and the induction below has no `0` case to run. -/
theorem primePowerProd_eq_factorization_prod (f : ℕ → ℕ → M) {n : ℕ} (hn : n ≠ 0) :
    primePowerProd f n = n.factorization.prod f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : 1 < n
    · have hp : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
      have hmem : n.minFac ∈ n.factorization.support := by
        simp [Nat.mem_primeFactors, hp, n.minFac_dvd, hn]
      have hlt : n / n.minFac ^ n.factorization n.minFac < n :=
        Nat.div_lt_self (by omega) (Nat.one_lt_pow
          (hp.factorization_pos_of_dvd hn n.minFac_dvd).ne' hp.one_lt)
      rw [primePowerProd_of_one_lt f h1, ih _ hlt (Nat.ordCompl_pos _ hn).ne',
        Nat.factorization_ordCompl, Finsupp.mul_prod_erase _ _ _ hmem]
    · have : n = 1 := by omega
      simp [this]

/-- **Multiplicativity on coprime arguments**: the blocks of `m * n` are exactly the blocks of
`m` together with those of `n` when `m` and `n` share no prime, and the two orderings differ by
a permutation the commutativity absorbs. -/
theorem primePowerProd_mul_of_coprime (f : ℕ → ℕ → M) {m n : ℕ} (hmn : Nat.Coprime m n) :
    primePowerProd f (m * n) = primePowerProd f m * primePowerProd f n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn
    simp [hmn]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn
    simp [hmn]
  rw [primePowerProd_eq_factorization_prod f (Nat.mul_ne_zero hm hn),
    primePowerProd_eq_factorization_prod f hm, primePowerProd_eq_factorization_prod f hn,
    Nat.factorization_mul_of_coprime hmn,
    Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors]

end CommMonoid

end Nat

end TauCeti
