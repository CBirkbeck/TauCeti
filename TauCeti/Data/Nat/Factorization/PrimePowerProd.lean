/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Prime.Pow

/-!
# Ordered products over a prime factorisation

`n.factorization.prod f` multiplies the blocks `f p (n.factorization p)` over the primes
dividing `n`. Being a `Finsupp.prod` it asks for a `CommMonoid`: a `Finsupp` records no order
on its support, so the product is only well defined once the factors commute.

`TauCeti.Nat.primePowerProd f n` multiplies the same blocks in a fixed order — least prime
first — and so asks only for `One` and `Mul`. Each step peels `Nat.minFac n` together with its
whole multiplicity, and recurses on `ordCompl[n.minFac] n`. Both `n = 0` and `n = 1` give the
empty product.

The ordering is not the point; the weakened typeclass is. A monoid that happens to be
commutative without carrying a `CommMonoid` *instance* — a Hecke ring whose commutativity is a
theorem rather than a structure field, say — cannot form `n.factorization.prod f` at all, and
this is what it forms instead. `primePowerProd_eq_factorization_prod` records that nothing is
lost: as soon as a `CommMonoid` instance is available the two agree.

Neither associativity nor a unit law enters the definition — the bracketing is fixed — so it is
stated at `One` plus `Mul`, in the same spirit as `List.prod`, which Lean defines at `Mul` plus
`One`. `mul_one` is needed once, to collapse the single block of a prime power. Associativity
enters with the multiplicativity on coprime arguments, which is stated in a `Monoid` under the
hypothesis it actually uses — each block of one argument commutes with each block of the other
— so that the monoid of the previous paragraph can use it. Only the `Finsupp.prod` comparison
needs the full `CommMonoid`.

## Main definitions

* `TauCeti.Nat.primePowerProd`: the product of `f p (n.factorization p)` over the primes of
  `n`, taken in increasing order of prime.

## Main results

* `TauCeti.Nat.primePowerProd_of_one_lt`: the peeling step, as a rewriting rule.
* `TauCeti.Nat.primePowerProd_prime_pow`: on a prime power the product is a single block.
* `Commute.primePowerProd_right`: an element commuting with every block commutes with the
  ordered product.
* `TauCeti.Nat.primePowerProd_mul_of_coprime`: multiplicativity on coprime arguments, given
  that the blocks of the two arguments commute.
* `TauCeti.Nat.primePowerProd_eq_factorization_prod`: in a `CommMonoid` it is
  `n.factorization.prod f`.

## Implementation notes

The definition is `Nat.recOnPrimePow`, which already performs the least-prime-power
decomposition this product runs over. That recursor is `@[elab_as_elim]` and mathlib states no
computation rules for it, so the three equations `primePowerProd_zero`, `primePowerProd_one`
and `primePowerProd_of_one_lt` are proved by unfolding it and `Nat.strongRec` once. Everything
after them goes through those equations and never through the body again.

Coprime multiplicativity is a strong induction on `m * n`. The least prime of `m * n` lies in
exactly one of the factors; when it lies in `m` the peeling step and the induction hypothesis
already give the answer, and when it lies in `n` the same argument with the roles of `m` and
`n` swapped gives the two ordered products in the wrong order, which is the one place the
commutation hypothesis is used.

## Provenance

Adapted from AINTLIB (see References): `peelProd` and its six companion lemmas, which sit in a
Hecke file inside the `HeckeRing.GL2.Unified` namespace. They are combinatorics about
`Nat.minFac` carrying no Hecke content, so they are lifted here. The source asks
`Monoid`/`CommMonoid` and writes the recursion out by hand; here the classes are weakened to
`One` plus `Mul`, the recursion is routed through mathlib's `Nat.recOnPrimePow`, the coprime
multiplicativity is proved in a `Monoid` from blockwise commutation instead of being read off
the `Finsupp.prod` comparison, and that comparison is stated for every `n` rather than only for
`n ≠ 0`. The comparison is `private` in the source and is exposed here, since it is the
statement tying the definition to mathlib's idiom.

## References

* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
  `projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`,
  lines 111-184.
-/

public section

namespace TauCeti

namespace Nat

/-- For `1 < n` the least prime factor of `n` is one of its primes. -/
private theorem minFac_mem_primeFactors {n : ℕ} (hn : 1 < n) : n.minFac ∈ n.primeFactors :=
  Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hn.ne', n.minFac_dvd, by omega⟩

/-- Peeling the block at the least prime factor makes `n` strictly smaller. -/
private theorem ordCompl_minFac_lt {n : ℕ} (hn : 1 < n) : ordCompl[n.minFac] n < n :=
  Nat.div_lt_self (by omega) (Nat.one_lt_pow
    ((Nat.minFac_prime hn.ne').factorization_pos_of_dvd (by omega) n.minFac_dvd).ne'
    (Nat.minFac_prime hn.ne').one_lt)

/-- A block of `ordCompl[p] n` is a block of `n`, at a prime other than `p`. -/
private theorem block_ordCompl {n p q : ℕ} (hq : q ∈ (ordCompl[p] n).primeFactors) :
    q ∈ n.primeFactors ∧ (ordCompl[p] n).factorization q = n.factorization q := by
  rw [← Nat.support_factorization, Nat.factorization_ordCompl, Finsupp.support_erase,
    Finset.mem_erase, Nat.support_factorization] at hq
  exact ⟨hq.2, by rw [Nat.factorization_ordCompl, Finsupp.erase_ne hq.1]⟩

variable {M : Type*}

section MulOne

variable [One M] [Mul M]

/-- The product of the blocks `f p (n.factorization p)` over the primes `p` dividing `n`, taken
in increasing order of `p`: each step peels off the least prime factor of `n` together with its
whole multiplicity. The empty product `1` is returned at `n = 1`, and at `n = 0` as a junk
value — `0` has no factorisation to run over.

Only `One M` and `Mul M` are asked, which is the whole point of the definition; see
`primePowerProd_eq_factorization_prod` for the agreement with `n.factorization.prod f` when `M`
is commutative. -/
noncomputable def primePowerProd (f : ℕ → ℕ → M) : ℕ → M :=
  Nat.recOnPrimePow 1 1 fun _ p v _ _ _ ih ↦ f p v * ih

@[simp]
theorem primePowerProd_zero (f : ℕ → ℕ → M) : primePowerProd f 0 = 1 := by
  unfold primePowerProd Nat.recOnPrimePow
  rw [Nat.strongRec_eq]

@[simp]
theorem primePowerProd_one (f : ℕ → ℕ → M) : primePowerProd f 1 = 1 := by
  unfold primePowerProd Nat.recOnPrimePow
  rw [Nat.strongRec_eq]

/-- **The peeling step**: for `1 < n` the ordered product splits off the block at `n.minFac`,
leaving the ordered product over `ordCompl[n.minFac] n`. -/
theorem primePowerProd_of_one_lt (f : ℕ → ℕ → M) {n : ℕ} (hn : 1 < n) : primePowerProd f n =
    f n.minFac (n.factorization n.minFac) *
      primePowerProd f (n / n.minFac ^ n.factorization n.minFac) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  unfold primePowerProd Nat.recOnPrimePow
  rw [Nat.strongRec_eq]
  rfl

end MulOne

section MulOneClass

variable [MulOneClass M]

/-- On a prime power the product is a single block: `primePowerProd f (p ^ v) = f p v`. The
hypothesis `v ≠ 0` is needed — at `v = 0` the left-hand side is the empty product `1` while the
right-hand side is `f p 0`, and nothing forces those to agree. -/
@[simp]
theorem primePowerProd_prime_pow (f : ℕ → ℕ → M) {p : ℕ} (hp : p.Prime) {v : ℕ} (hv : v ≠ 0) :
    primePowerProd f (p ^ v) = f p v := by
  simpa [hp.pow_minFac hv, hp.factorization_self, Nat.div_self (pow_pos hp.pos v)]
    using primePowerProd_of_one_lt f (Nat.one_lt_pow hv hp.one_lt)

end MulOneClass

section Monoid

variable [Monoid M]

/-- An element commuting with every block of `n` commutes with their ordered product. -/
theorem _root_.Commute.primePowerProd_right (f : ℕ → ℕ → M) {x : M} {n : ℕ}
    (h : ∀ p ∈ n.primeFactors, Commute x (f p (n.factorization p))) :
    Commute x (primePowerProd f n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : 1 < n
    · rw [primePowerProd_of_one_lt f hn]
      refine (h _ (minFac_mem_primeFactors hn)).mul_right (ih _ (ordCompl_minFac_lt hn) ?_)
      intro q hq
      rw [(block_ordCompl hq).2]
      exact h q (block_ordCompl hq).1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (not_lt.1 hn) with rfl | rfl <;> simp

/-- The case of `primePowerProd_mul_of_coprime` in which the least prime of `m * n` lies in
`m`, given the induction hypothesis for smaller products: the block at `m.minFac` splits off,
`ordCompl[m.minFac] m * n` is handled by `ih`, and `primePowerProd_of_one_lt` reassembles
`primePowerProd f m`. No commutation is needed here. -/
private theorem primePowerProd_mul_of_minFac_dvd (f : ℕ → ℕ → M) {m n : ℕ} (hmn : m.Coprime n)
    (h1 : 1 < m * n) (hr : (m * n).minFac ∣ m)
    (ih : ∀ {m' n' : ℕ}, m' * n' < m * n → m'.Coprime n' →
      (∀ p ∈ m'.primeFactors, ∀ q ∈ n'.primeFactors,
        Commute (f p (m'.factorization p)) (f q (n'.factorization q))) →
      primePowerProd f (m' * n') = primePowerProd f m' * primePowerProd f n')
    (hf : ∀ p ∈ m.primeFactors, ∀ q ∈ n.primeFactors,
      Commute (f p (m.factorization p)) (f q (n.factorization q))) :
    primePowerProd f (m * n) = primePowerProd f m * primePowerProd f n := by
  have hrp := Nat.minFac_prime h1.ne'
  have hn0 : n ≠ 0 := by rintro rfl; simp at h1
  have hm1 : 1 < m :=
    hrp.two_le.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (by rintro rfl; simp at h1)) hr)
  have hrn : ¬(m * n).minFac ∣ n :=
    hrp.coprime_iff_not_dvd.1 (Nat.Coprime.coprime_dvd_left hr hmn)
  have hmin : m.minFac = (m * n).minFac :=
    le_antisymm (Nat.minFac_le_of_dvd hrp.two_le hr)
      (Nat.minFac_le_of_dvd (Nat.minFac_prime hm1.ne').two_le (m.minFac_dvd.mul_right n))
  rw [primePowerProd_of_one_lt f h1, Nat.ordCompl_mul, Nat.factorization_mul_of_coprime hmn,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hrn, add_zero, pow_zero, Nat.div_one,
    ← hmin, ih (Nat.mul_lt_mul_of_pos_right (ordCompl_minFac_lt hm1) (Nat.pos_of_ne_zero hn0))
      (Nat.Coprime.coprime_dvd_left (Nat.ordCompl_dvd m _) hmn) (fun p hp q hq ↦ by
        rw [(block_ordCompl hp).2]; exact hf p (block_ordCompl hp).1 q hq),
    ← mul_assoc, ← primePowerProd_of_one_lt f hm1]

/-- **Multiplicativity on coprime arguments.** When `m` and `n` share no prime, the blocks of
`m * n` are the blocks of `m` together with those of `n`, interleaved by size; moving the blocks
of `n` past those of `m` is exactly what the commutation hypothesis allows. In a `CommMonoid`
it is discharged by `fun _ _ _ _ ↦ Commute.all _ _`. -/
theorem primePowerProd_mul_of_coprime (f : ℕ → ℕ → M) {m n : ℕ} (hmn : m.Coprime n)
    (hf : ∀ p ∈ m.primeFactors, ∀ q ∈ n.primeFactors,
      Commute (f p (m.factorization p)) (f q (n.factorization q))) :
    primePowerProd f (m * n) = primePowerProd f m * primePowerProd f n := by
  obtain ⟨k, hk⟩ : ∃ k, m * n = k := ⟨_, rfl⟩
  induction k using Nat.strong_induction_on generalizing m n with
  | _ k ih =>
  subst hk
  by_cases h1 : 1 < m * n
  swap
  · obtain h0 | h0 : m * n = 0 ∨ m * n = 1 := by omega
    · rcases Nat.mul_eq_zero.1 h0 with rfl | rfl
      · simp [(Nat.coprime_zero_left _).1 hmn]
      · simp [(Nat.coprime_zero_right _).1 hmn]
    · obtain ⟨rfl, rfl⟩ : m = 1 ∧ n = 1 :=
        ⟨Nat.eq_one_of_mul_eq_one_right h0, Nat.eq_one_of_mul_eq_one_left h0⟩
      simp
  rcases (Nat.minFac_prime h1.ne').dvd_mul.1 (Nat.minFac_dvd _) with hr | hr
  · exact primePowerProd_mul_of_minFac_dvd f hmn h1 hr (fun hlt hc hf' ↦ ih _ hlt hc hf' rfl) hf
  · rw [mul_comm m n] at h1 hr ih ⊢
    refine (primePowerProd_mul_of_minFac_dvd f hmn.symm h1 hr
      (fun hlt hc hf' ↦ ih _ hlt hc hf' rfl) fun q hq p hp ↦ (hf p hp q hq).symm).trans ?_
    exact (Commute.primePowerProd_right f fun q hq ↦
      (Commute.primePowerProd_right f fun p hp ↦ (hf p hp q hq).symm).symm).symm.eq

end Monoid

section CommMonoid

variable [CommMonoid M]

/-- Once the factors commute the ordering is invisible and the ordered product is the
`Finsupp.prod` over the factorisation. Unconditional in `n`, so it rewrites without a side
goal: at `n = 0` both sides are `1`, the left as the junk value and the right because
`Nat.factorization 0 = 0` has empty support. -/
@[simp]
theorem primePowerProd_eq_factorization_prod (f : ℕ → ℕ → M) (n : ℕ) :
    primePowerProd f n = n.factorization.prod f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : 1 < n
    · calc primePowerProd f n
          = f n.minFac (n.factorization n.minFac) *
              primePowerProd f (ordCompl[n.minFac] n) := primePowerProd_of_one_lt f h1
        _ = f n.minFac (n.factorization n.minFac) *
              (n.factorization.erase n.minFac).prod f := by
            rw [ih _ (ordCompl_minFac_lt h1), Nat.factorization_ordCompl]
        _ = n.factorization.prod f := Finsupp.mul_prod_erase _ _ _ (minFac_mem_primeFactors h1)
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (not_lt.1 h1) with rfl | rfl <;> simp

end CommMonoid

end Nat

end TauCeti
