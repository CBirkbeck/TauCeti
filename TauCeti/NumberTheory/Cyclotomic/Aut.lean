/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Order and cyclicity of a cyclotomic Galois group

Mathlib's `IsCyclotomicExtension.autEquivPow` identifies `Gal(L / K)` with `(ZMod n)ˣ` as soon as
`Φ_n` is irreducible over `K`. This file records the two numerical consequences, which are what a
counting argument consumes: the *order* of that group is `φ n`, and it is *cyclic* whenever
`(ZMod n)ˣ` is — in particular whenever `n` is prime, where the order reads `n - 1`.

## Main results

* `IsCyclotomicExtension.card_aut_eq_totient`: `#Gal(L / K) = φ n`.
* `IsCyclotomicExtension.isCyclic_aut`: the group is cyclic when `(ZMod n)ˣ` is.
* `IsCyclotomicExtension.card_aut_eq_sub_one` and `IsCyclotomicExtension.isCyclic_aut_of_prime`:
  the prime case, where the order is `q - 1` and the group is always cyclic.

## Implementation notes

The equivalence itself is Mathlib's and is deliberately not restated here: `autEquivPow L h` is
already the isomorphism, and naming the composite would duplicate it. What is not available is the
order and the cyclicity, both of which need a fact about `(ZMod n)ˣ` — `ZMod.card_units_eq_totient`
and `ZMod.isCyclic_units_prime` respectively — rather than the equivalence alone.

`Nat.card` is used rather than `Fintype.card` so that no finiteness instance is demanded of the
caller; the finiteness needed in the proof is supplied locally from `NeZero n`.

The two prime specialisations are kept even though each is two rewrites from the general form,
because they are the shape the Chebotarev development asks for by name. Its roadmap states Layer
7.2 as "`[K(ζ_q) : K] = q - 1` … in particular cyclic of order `q - 1`", and Layer 9 opens "By
7.2, `H_q` is cyclic of order `q - 1`". Making every such caller re-derive `Nat.totient_prime` and
re-instantiate `ZMod.isCyclic_units_prime` is the duplication these two avoid. `q - 1` is
truncated subtraction, so the prime hypothesis has to be in scope for the statement to mean what
it says; that is why the specialisation is a theorem rather than a `simp` lemma.
-/

public section

open Polynomial

namespace IsCyclotomicExtension

section General

variable {n : ℕ} [NeZero n] (K : Type*) [Field K] (L : Type*) [CommRing L] [IsDomain L]
  [Algebra K L] [IsCyclotomicExtension {n} K L]

/-- **The order of a cyclotomic Galois group.** If `Φ_n` is irreducible over `K` then the Galois
group of an `n`-th cyclotomic extension of `K` has exactly `φ n` elements.

This is `IsCyclotomicExtension.autEquivPow` composed with `ZMod.card_units_eq_totient`. -/
theorem card_aut_eq_totient (h : Irreducible (cyclotomic n K)) :
    Nat.card (L ≃ₐ[K] L) = n.totient := by
  rw [Nat.card_congr (autEquivPow L h).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

/-- **A cyclotomic Galois group is cyclic when the unit group is.** Transported along
`IsCyclotomicExtension.autEquivPow`. -/
theorem isCyclic_aut [IsCyclic (ZMod n)ˣ] (h : Irreducible (cyclotomic n K)) :
    IsCyclic (L ≃ₐ[K] L) :=
  isCyclic_of_surjective _ (autEquivPow L h).symm.surjective

end General

section Prime

variable {q : ℕ} (K : Type*) [Field K] (L : Type*) [CommRing L] [IsDomain L] [Algebra K L]

/-- **The prime case: the order is `q - 1`.** For a `q`-th cyclotomic extension with `q` prime and
`Φ_q` irreducible over `K`, the Galois group has `q - 1` elements. -/
theorem card_aut_eq_sub_one (hq : q.Prime) [IsCyclotomicExtension {q} K L]
    (h : Irreducible (cyclotomic q K)) : Nat.card (L ≃ₐ[K] L) = q - 1 := by
  have : NeZero q := ⟨hq.ne_zero⟩
  rw [card_aut_eq_totient K L h, Nat.totient_prime hq]

/-- **The prime case: the group is cyclic.** `(ZMod q)ˣ` is cyclic for `q` prime, so the Galois
group of a `q`-th cyclotomic extension is too. -/
theorem isCyclic_aut_of_prime (hq : q.Prime) [IsCyclotomicExtension {q} K L]
    (h : Irreducible (cyclotomic q K)) : IsCyclic (L ≃ₐ[K] L) := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime hq
  exact isCyclic_aut K L h

end Prime

end IsCyclotomicExtension
