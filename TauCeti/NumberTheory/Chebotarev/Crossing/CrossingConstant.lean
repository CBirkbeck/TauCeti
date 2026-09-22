/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Crossing.TaggedCount

/-!
# The crossing constant of an auxiliary cyclic group

The cyclotomic crossing bounds the density of a Frobenius fibre from below by a quantity built
from one auxiliary prime: the proportion of the product `Gal(L/K) × H` taken up by the tags, where
`H` is the auxiliary cyclic group and a tag is an element of `H` whose order is divisible by the
residue degree `f`.  This file defines that proportion, `crossingConstant`, and bounds it below.

What the bound provides is uniformity: it depends on `f` only through the number of primes
dividing `f`, and on the auxiliary group only through the level `r` in `f ^ r ∣ #H`, so a consumer
that can raise `r` gets a bound approaching `1 / #Gal(L/K)` without revisiting this file.

## Main definitions

* `TauCeti.NumberField.Chebotarev.crossingConstant`: the proportion of `Gal(L/K) × H` occupied by
  the tagged elements.

## Main results

* `TauCeti.NumberField.Chebotarev.le_crossingConstant`: the same bound divided through by the
  order of the Galois group.

## References

The crossing construction follows R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
-/

public section

namespace TauCeti.NumberField.Chebotarev

open Finset

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable {H : Type*} [Group H] [Fintype H]

/-- **The crossing constant.**  The proportion of `Gal(L/K) × H` taken up by the tagged elements
of the auxiliary cyclic group `H`: those whose order is divisible by `f`.

The Galois group enters only through its order, as the denominator that turns a count of tags into
the density contributed by one auxiliary prime. -/
noncomputable def crossingConstant (f : ℕ) : ℝ :=
  ((taggedElements (H := H) f).card : ℝ) /
    ((Nat.card (L ≃ₐ[K] L) : ℝ) * (Nat.card H : ℝ))

/-- `crossingConstant` unfolded to the ratio defining it: the rewrite rule that turns the constant
into the count it abbreviates. -/
@[simp]
theorem crossingConstant_def (f : ℕ) : crossingConstant K L (H := H) f =
    ((taggedElements (H := H) f).card : ℝ) /
      ((Nat.card (L ≃ₐ[K] L) : ℝ) * (Nat.card H : ℝ)) :=
  (rfl)

/-- **The lower bound for the crossing constant.**  When `f ^ r` divides the order of the cyclic
auxiliary group `H`, the crossing constant is at least `(1 - 2 ^ (-r)) ^ #f.primeFactors` divided
by the order of `Gal(L/K)`.  The bound no longer mentions `#H`: the auxiliary group enters only
through the level `r`.

`Gal(L/K)` is not assumed finite; when it is infinite both sides are `0`. -/
theorem le_crossingConstant [IsCyclic H] (f r : ℕ) (hrpos : 0 < r) (hf : f ^ r ∣ Nat.card H) :
    (1 - (2 : ℝ) ^ (-(r : ℤ))) ^ f.primeFactors.card / (Nat.card (L ≃ₐ[K] L) : ℝ) ≤
      crossingConstant K L (H := H) f := by
  rw [crossingConstant_def, div_mul_eq_div_div_swap]
  gcongr
  exact (le_div_iff₀ (mod_cast Nat.card_pos)).mpr <| le_card_taggedElements_cyclic f r hrpos hf

end TauCeti.NumberField.Chebotarev
