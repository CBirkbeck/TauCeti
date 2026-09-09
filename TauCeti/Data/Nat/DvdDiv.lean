/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Init

/-!
# Dividing one factor out of a square divisor

If `p²` divides `N`, then one factor of `p` survives the division: `p` still divides `N / p`.
That is the shape divisibility takes when a prime is removed from a level one power at a time.

`Nat.dvd_div_iff_mul_dvd` already turns `p ∣ N / p` into `p * p ∣ N`, but only once `p ∣ N` is in
hand. What this file records is that `p ^ 2 ∣ N` supplies *both* — the outer divisibility and the
side condition — so callers need no separate hypothesis.

## Main results

* `TauCeti.Nat.dvd_div_of_sq_dvd`: `p ^ 2 ∣ N → p ∣ N / p`.
-/

public section

namespace TauCeti

namespace Nat

/-- **One factor of a square divisor survives the division.** From `p ^ 2 ∣ N` alone, `p` divides
`N / p`: the same hypothesis gives `p ∣ N`, so the division is exact, and `p * p ∣ N` is what
`Nat.dvd_div_iff_mul_dvd` asks for. -/
theorem dvd_div_of_sq_dvd {p N : ℕ} (hpsq : p ^ 2 ∣ N) : p ∣ N / p := by
  rw [Nat.pow_two] at hpsq
  exact (Nat.dvd_div_iff_mul_dvd (Nat.dvd_trans ⟨p, rfl⟩ hpsq)).mpr hpsq

end Nat

end TauCeti
