/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

end IsMultiplicative

end ArithmeticFunction
