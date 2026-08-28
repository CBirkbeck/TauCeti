/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Data.Nat.Log

/-!
# The `p`-adic valuation is sublinear

`n - padicValNat p n → ∞` for `1 < p`. This is the `padicValNat` counterpart of
`tendsto_sub_log_atTop`, and follows from it because the `p`-adic valuation is dominated by the
base-`p` logarithm (`padicValNat_le_nat_log`).

Mathlib carries no asymptotic statement about `padicValNat`, and this is the form consumers want:
subtracting the valuation from `n` still leaves something tending to infinity, so a construction
may spend `padicValNat p n` of its budget and retain unbounded room.

## Main results

* `tendsto_sub_padicValNat_atTop` : `n - padicValNat p n → ∞` for `1 < p`.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`,
  `EllipticCurves/Mathlib/Chabauty/PadicValNat.lean`. The proof is that file's.
-/

public section

open Filter

/-- `n - v_p(n) → ∞`: the `p`-adic valuation is sublinear. -/
theorem tendsto_sub_padicValNat_atTop {p : ℕ} (hp : 1 < p) :
    Tendsto (fun n ↦ n - padicValNat p n) atTop atTop :=
  tendsto_atTop_mono (fun n ↦ Nat.sub_le_sub_left (padicValNat_le_nat_log n) n)
    (tendsto_sub_log_atTop hp)

end
