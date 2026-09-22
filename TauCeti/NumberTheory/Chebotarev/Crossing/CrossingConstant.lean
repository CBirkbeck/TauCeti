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
from one auxiliary prime: the proportion of the auxiliary cyclic group `H` taken up by the tags —
the elements whose order is divisible by the residue degree `f` — divided in addition by the order
of `Aut_K(L)`.  Equivalently it is the proportion of `Aut_K(L) × H` represented by one
automorphism paired with the tags.  This file defines that quantity, `crossingConstant`, and
bounds it below.

What the bound provides is uniformity: it depends on `f` only through the number of primes
dividing `f`, and on the auxiliary group only through the level `r` in `f ^ r ∣ #H`, so a consumer
that can raise `r` gets a bound approaching `1 / #Aut_K(L)` without revisiting this file.

## Main definitions

* `TauCeti.NumberField.Chebotarev.crossingConstant`: the tag proportion in `H`, divided by the
  order of `Aut_K(L)`.

## Main results

* `TauCeti.NumberField.Chebotarev.le_crossingConstant`: the same bound divided through by the
  order of the Galois group.

## References

The crossing construction follows R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
-/

public section

namespace TauCeti.NumberField.Chebotarev

open Finset

variable (K L : Type*) [CommSemiring K] [Semiring L] [Algebra K L]
variable {H : Type*} [Group H] [Fintype H]

/-- **The crossing constant.**  The number of tagged elements of the auxiliary cyclic group `H` —
those whose order is divisible by `f` — divided by `#Aut_K(L) * #H`.

That is the tag proportion within `H`, divided in addition by the order of `Aut_K(L)`, which
enters only through its order: the denominator that turns a count of tags into the density
contributed by one auxiliary prime. -/
noncomputable def crossingConstant (f : ℕ) : ℝ :=
  ((taggedElements (H := H) f).card : ℝ) /
    ((Nat.card (L ≃ₐ[K] L) : ℝ) * (Nat.card H : ℝ))

/-- **The lower bound for the crossing constant.**  When `f ^ r` divides the order of the cyclic
auxiliary group `H`, the crossing constant is at least `(1 - 2 ^ (-r)) ^ #f.primeFactors` divided
by the order of `Aut_K(L)`.  The bound no longer mentions `#H`: the auxiliary group enters only
through the level `r`.

`Aut_K(L)` is not assumed finite; when it is infinite both sides are `0`. -/
theorem le_crossingConstant [IsCyclic H] (f r : ℕ) (hrpos : 0 < r) (hf : f ^ r ∣ Nat.card H) :
    (1 - (2 : ℝ) ^ (-(r : ℤ))) ^ f.primeFactors.card / (Nat.card (L ≃ₐ[K] L) : ℝ) ≤
      crossingConstant K L (H := H) f := by
  rw [crossingConstant, div_mul_eq_div_div_swap]
  gcongr
  exact (le_div_iff₀ (mod_cast Nat.card_pos)).mpr <| le_card_taggedElements_cyclic f r hrpos hf

end TauCeti.NumberField.Chebotarev
