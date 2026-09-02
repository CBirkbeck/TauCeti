/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Frobenius

/-!
# Frobenius elements for a group acting on a ring extension

This file supplements Mathlib's `IsArithFrobAt` API with two facts about a group acting on a
commutative ring extension `S/R`. Both are stated at ring level, so they are available
independently of any number-field or Legendre-symbol specialization.

For an ideal `p` of `R`, an element `σ` of the acting group cuts out the set of primes of `S` above
`p` that admit `σ` as an arithmetic Frobenius. These sets need not be disjoint: at a ramified prime
several elements are a Frobenius at once, so this is a family of fibers rather than a partition.
Where the extension is unramified `IsArithFrobAt.eq_of_isUnramifiedAt` makes the fibers disjoint,
and they exhaust the primes above `p` exactly when a Frobenius exists at each of them — which needs
hypotheses of its own, such as those of `IsArithFrobAt.exists_of_isInvariant`.

## Main results

* `IsArithFrobAt.eq_of_isUnramifiedAt` — a Frobenius element is unique for a faithful action at an
  unramified prime.
* `TauCeti.frobeniusFiber_card_eq_of_isConj` — conjugate elements have equipotent fibers above a
  fixed ideal of the base.

The second is the "distributed evenly" step of Chebotarev's density theorem: where the fibers do
partition the primes above `p`, it is what lets a count over a whole conjugacy class be recovered
from the count at a single representative.

## Implementation notes

The bijection realizing the equipotence is not conjugation itself but the pointwise action
`P ↦ c • P` of a witnessing element `c`; Mathlib's `IsArithFrobAt.conj` is what transports the
Frobenius condition along it, sending a Frobenius `σ` at `P` to the Frobenius `c * σ * c⁻¹` at
`c • P`.

The source states the equipotence for the rings of integers of a Galois extension of number
fields and under an unramifiedness hypothesis on `p` that it never uses. Both restrictions are
dropped here: the transport argument uses only the generic Frobenius group-action API, and it is
available at every prime.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (p. 143).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix.
* Birkbeck–Brasca, [chebotarev-density](https://github.com/CBirkbeck/chebotarev-density)
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/FixedFieldDensity.lean`, declaration `frobeniusFibre_card_eq_of_isConj`
  (source line 54). The statement and proof of `frobeniusFiber_card_eq_of_isConj` below are
  adapted from that declaration.
-/

public section

open nonZeroDivisors

open scoped Pointwise

namespace TauCeti

/-- Suppose `S` is Noetherian and `Q` is a prime of `S` containing all zero-divisors. If the
action of `G` on `S` is faithful and the extension is unramified at `Q`, then a Frobenius element
of `G` at `Q` is unique. -/
theorem _root_.IsArithFrobAt.eq_of_isUnramifiedAt
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Monoid G]
    [MulSemiringAction G S] [SMulCommClass G R S] [FaithfulSMul G S]
    {Q : Ideal S} [Q.IsPrime] (hQ : Q.primeCompl ≤ S⁰)
    [Algebra.IsUnramifiedAt R Q] [IsNoetherianRing S]
    {σ τ : G} (hσ : _root_.IsArithFrobAt R σ Q) (hτ : _root_.IsArithFrobAt R τ Q) : σ = τ := by
  apply MulSemiringAction.toAlgHom_injective R S
  exact AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ hτ hQ

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [SMulCommClass G R S]

private theorem exists_isArithFrobAt_smul {p : Ideal R} {σ τ c : G} {P : Ideal S}
    (hτ : c * σ * c⁻¹ = τ)
    (h : ∃ (_ : P.IsPrime) (_ : P.LiesOver p) (_ : P ≠ ⊥), IsArithFrobAt R σ P) :
    ∃ (_ : (c • P).IsPrime) (_ : (c • P).LiesOver p) (_ : c • P ≠ ⊥),
      IsArithFrobAt R τ (c • P) := by
  obtain ⟨_, _, hne, hfrob⟩ := h
  refine ⟨inferInstance, inferInstance, ?_, hτ ▸ hfrob.conj c⟩
  simpa using (MulAction.injective c).ne hne

/-- **Equipotent Frobenius fibers.** For `IsConj σ σ'`, the nonzero primes of `S` above `p` with
arithmetic Frobenius `σ` are equal in number to those with arithmetic Frobenius `σ'`. -/
theorem frobeniusFiber_card_eq_of_isConj (p : Ideal R) (σ σ' : G) (hc : IsConj σ σ') :
    Nat.card {P : Ideal S // ∃ (_ : P.IsPrime) (_ : P.LiesOver p) (_ : P ≠ ⊥),
        IsArithFrobAt R σ P} =
      Nat.card {P : Ideal S // ∃ (_ : P.IsPrime) (_ : P.LiesOver p) (_ : P ≠ ⊥),
        IsArithFrobAt R σ' P} := by
  -- conjugating by a witnessing element `c` is the bijection between the two fibers
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm c) fun P ↦ ?_)
  simp only [MulAction.toPerm_apply]
  refine ⟨exists_isArithFrobAt_smul rfl, fun h ↦ ?_⟩
  -- the reverse direction is the same transport along `c⁻¹`
  simpa using exists_isArithFrobAt_smul (c := c⁻¹) (τ := σ) (by group) h

end TauCeti
