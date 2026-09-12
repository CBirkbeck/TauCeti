/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Multiplication on the one-point extension of `ZMod p`

`ZMod.mulModEquiv` (`Data/ZMod/FinEquiv.lean`) is multiplication by a unit as a permutation of
the residues themselves. This file is its companion on the one-point extension: multiplication by
a `d` coprime to `p`, acting on `OnePoint (ZMod p)` and fixing `∞`.

`p` is unrestricted here, so `OnePoint (ZMod p)` is only the affine line with a point adjoined.
It is the projective line exactly when `p` is prime: for composite `p` the projective line over
`ZMod p` is larger, carrying `p * ∏ (1 + 1 / ℓ)` points over the primes `ℓ ∣ p` rather than
`p + 1`. Nothing below needs the identification, so nothing below assumes `p` prime.

## Main results

* `ZMod.onePointMulPerm`: multiplication by `d` as a permutation of `OnePoint (ZMod p)`.
* `ZMod.onePointMulPerm_coe` and `ZMod.onePointMulPerm_infty`: its two evaluation rules, on an
  affine point and at `∞`.
-/

public section

namespace ZMod

/-- **Multiplication by `d` on the one-point extension of `ZMod p`**, fixing `∞`. The companion
of `ZMod.mulModEquiv`: `d` coprime to `p` is a unit, so multiplying by it permutes the residues,
and the permutation is extended by fixing the adjoined point. -/
def onePointMulPerm (p : ℕ) {d : ℕ} (hdp : Nat.Coprime d p) :
    Equiv.Perm (OnePoint (ZMod p)) :=
  Equiv.optionCongr (Units.mulLeft (ZMod.unitOfCoprime d hdp))

/-- **The value of `ZMod.onePointMulPerm` at an affine point**: it multiplies by `d`. -/
@[simp]
lemma onePointMulPerm_coe (p : ℕ) {d : ℕ} (hdp : Nat.Coprime d p) (x : ZMod p) :
    onePointMulPerm p hdp ((x : ZMod p) : OnePoint (ZMod p)) =
      (((d : ZMod p) * x : ZMod p) : OnePoint (ZMod p)) := by
  -- `OnePoint (ZMod p)` is `Option (ZMod p)` by definition but is a plain `def`, so it does not
  -- unfold at reducible transparency: `Equiv.optionCongr_apply` does not match an application
  -- typed at `OnePoint`, and neither `simp [onePointMulPerm]` nor a rewrite with it closes the
  -- goal. `change` restates the value at the definitional unfolding, where `mulLeft` evaluates.
  change ((((ZMod.unitOfCoprime d hdp : (ZMod p)ˣ) : ZMod p) * x : ZMod p) :
      OnePoint (ZMod p)) = _
  rw [ZMod.coe_unitOfCoprime]

/-- **`ZMod.onePointMulPerm` fixes the point at infinity.** -/
@[simp]
lemma onePointMulPerm_infty (p : ℕ) {d : ℕ} (hdp : Nat.Coprime d p) :
    onePointMulPerm p hdp (OnePoint.infty : OnePoint (ZMod p)) = OnePoint.infty := (rfl)

end ZMod
