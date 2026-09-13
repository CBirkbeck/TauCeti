/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Multiplicative functions with a common prime-power recurrence

A Hecke eigensystem is multiplicative and satisfies, at every prime `p`, the recurrence

```text
a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - w p * a (p ^ r),
```

whose weight `w p` depends on the level and weight but **not** on the eigenform. This file
records what that shared recurrence buys: such a function is determined by its values at the
primes alone, so two of them that agree at every prime are equal.

## Main results

* `ArithmeticFunction.IsMultiplicative.eq_of_eq_on_primes_of_rec`: two multiplicative functions
  obeying the same recurrence and agreeing at every prime are equal.
* `ArithmeticFunction.IsMultiplicative.exists_prime_ne_of_ne_of_rec`: contrapositively, two
  distinct such functions differ at some prime.
-/

public section

namespace ArithmeticFunction

variable {R : Type*} [CommRing R]

/-- **A common prime-power recurrence**: `f (p ^ (r + 2)) = f p * f (p ^ (r + 1)) - w p * f (p ^ r)`
at every prime `p`, with the weight `w` a function of the prime alone. For Hecke eigensystems
`w p = χ p * p ^ (k - 1)`, which is why the weight is shared by every eigenform of a given level
and weight — and that sharing is what the results here need. -/
def HasPrimePowerRec (f : ArithmeticFunction R) (w : ℕ → R) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ r : ℕ, f (p ^ (r + 2)) = f p * f (p ^ (r + 1)) - w p * f (p ^ r)

namespace IsMultiplicative

/-- **Prime values determine prime-power values, given a shared recurrence.** Two multiplicative
functions obeying the same recurrence and agreeing at every prime agree at every prime power:
the recurrence propagates the agreement upward from `r = 0, 1`. -/
theorem eq_on_prime_pow_of_eq_on_primes_of_rec {f g : ArithmeticFunction R} {w : ℕ → R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (hfr : HasPrimePowerRec f w) (hgr : HasPrimePowerRec g w)
    (hp : ∀ p : ℕ, p.Prime → f p = g p) {p : ℕ} (hprime : p.Prime) (a : ℕ) :
    f (p ^ a) = g (p ^ a) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 => rw [pow_zero, hf.1, hg.1]
    | 1 => simpa using hp p hprime
    | (r + 2) =>
      rw [hfr p hprime r, hgr p hprime r, hp p hprime, ih (r + 1) (by omega), ih r (by omega)]

/-- **Two multiplicative functions with a common recurrence agreeing at the primes are equal.**
`ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers` reduces equality to the prime
powers, and `eq_on_prime_pow_of_eq_on_primes_of_rec` supplies those. -/
theorem eq_of_eq_on_primes_of_rec {f g : ArithmeticFunction R} {w : ℕ → R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (hfr : HasPrimePowerRec f w) (hgr : HasPrimePowerRec g w)
    (hp : ∀ p : ℕ, p.Prime → f p = g p) : f = g :=
  (eq_iff_eq_on_prime_powers f hf g hg).2 fun _p a hprime ↦
    eq_on_prime_pow_of_eq_on_primes_of_rec hf hg hfr hgr hp hprime a

/-- **Distinct multiplicative functions with a common recurrence differ at a prime.** The
contrapositive of `eq_of_eq_on_primes_of_rec`, and the form the independence argument uses: it
is what lets a minimal relation be cut down at a single prime. -/
theorem exists_prime_ne_of_ne_of_rec {f g : ArithmeticFunction R} {w : ℕ → R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (hfr : HasPrimePowerRec f w) (hgr : HasPrimePowerRec g w) (hne : f ≠ g) :
    ∃ p : ℕ, p.Prime ∧ f p ≠ g p := by
  by_contra hcon
  refine hne (eq_of_eq_on_primes_of_rec hf hg hfr hgr fun p hprime ↦ ?_)
  by_contra hne'
  exact hcon ⟨p, hprime, hne'⟩

/-- **Multiplying a vanishing relation by the value at a prime keeps it vanishing.** If
`∑ᵢ cᵢ · Gᵢ n = 0` for every `n ≥ 1` then so is `∑ᵢ cᵢ · Gᵢ p · Gᵢ n`: splitting `n = p ^ a · m`
with `p ∤ m`, the shared recurrence rewrites `Gᵢ p · Gᵢ (p ^ a)` as
`Gᵢ (p ^ (a+1)) + w p · Gᵢ (p ^ (a-1))`, and both resulting sums are instances of the original
relation. **This is the step that needs the weight to be shared by every `i`** — otherwise `w p`
could not be pulled out of the sum. -/
theorem sum_mul_prime_eq_zero {ι : Type*} {w : ℕ → R} {s : Finset ι}
    {G : ι → ArithmeticFunction R} (hmul : ∀ i ∈ s, (G i).IsMultiplicative)
    (hrec : ∀ i ∈ s, HasPrimePowerRec (G i) w) {c : ι → R}
    (hrel : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ s, c i * G i n = 0)
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ s, c i * (G i p * G i n) = 0 := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have hp0 : p ≠ 0 := hp.pos.ne'
  -- split off the `p`-part once and for all, keeping the cofactor opaque
  obtain ⟨a, m, hm0, hcop, rfl⟩ : ∃ a m, m ≠ 0 ∧ Nat.Coprime p m ∧ n = p ^ a * m :=
    ⟨n.factorization p, ordCompl[p] n, (Nat.ordCompl_pos p hn0).ne',
      Nat.coprime_ordCompl hp hn0, (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩
  have harg : ∀ k : ℕ, 1 ≤ p ^ k * m := fun k ↦
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero k hp0) hm0)
  have hpm : ∀ i ∈ s, ∀ k : ℕ, G i (p ^ k * m) = G i (p ^ k) * G i m :=
    fun i hi k ↦ (hmul i hi).2 (Nat.Coprime.pow_left k hcop)
  match a with
  | 0 =>
    -- `p ∤ n`: the prime value merges straight into the argument
    have hcop' : Nat.Coprime p (p ^ 0 * m) := by simpa using hcop
    have hmerge : ∀ i ∈ s, c i * (G i p * G i (p ^ 0 * m)) = c i * G i (p * (p ^ 0 * m)) :=
      fun i hi ↦ by rw [(hmul i hi).2 hcop']
    rw [Finset.sum_congr rfl hmerge]
    exact hrel _ (Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero hp0 (Nat.one_le_iff_ne_zero.1 (harg 0))))
  | (r + 1) =>
    -- `p ∣ n`: the recurrence trades one factor of `Gᵢ p` for two lower arguments
    have hstep : ∀ i ∈ s, c i * (G i p * G i (p ^ (r + 1) * m)) =
        c i * G i (p ^ (r + 2) * m) + w p * (c i * G i (p ^ r * m)) := fun i hi ↦ by
      have hkey : G i p * G i (p ^ (r + 1)) = G i (p ^ (r + 2)) + w p * G i (p ^ r) := by
        rw [hrec i hi p hp r]; ring
      rw [hpm i hi (r + 1), hpm i hi (r + 2), hpm i hi r]
      calc c i * (G i p * (G i (p ^ (r + 1)) * G i m))
          = c i * (G i p * G i (p ^ (r + 1)) * G i m) := by ring
        _ = c i * ((G i (p ^ (r + 2)) + w p * G i (p ^ r)) * G i m) := by rw [hkey]
        _ = _ := by ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum,
      hrel _ (harg (r + 2)), hrel _ (harg r), mul_zero, add_zero]

end IsMultiplicative

end ArithmeticFunction
