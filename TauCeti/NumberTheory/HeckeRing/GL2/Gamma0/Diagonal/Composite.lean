/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Factorization.PrimePowerProd
public import TauCeti.Algebra.PrimePowerProd.DivisorTable
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimePower
-- The Atkin–Lehner anti-involution and the commutativity it buys are used only inside the
-- proof of `heckeTCompositeGamma0_mul_of_coprime` below, so private.
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.AtkinLehner

/-!
# The composite diagonal element of the `Γ₀(N)` Hecke ring

`Diagonal/PrimePower.lean` builds the generator `T_p` and the family `T_{p^r}` that the
Diamond–Shurman recurrence produces, and closes by naming its own gap: "the composite element
assembled over a prime factorisation is [not] proved here". This file assembles it.

`heckeTCompositeGamma0 N n` multiplies the blocks `heckeTGeneratorRecGamma0 N p (v_p n)` over
the primes of `n`, least prime first. The assembly is `TauCeti.Nat.primePowerProd` rather than
`n.factorization.prod`: a `Finsupp.prod` needs a `CommMonoid` instance, and the Hecke ring
`𝕋 (Δ₀(N)) (Γ₀(N)) ℤ` carries only a `Ring` one — its commutativity is a theorem about the
Atkin–Lehner anti-involution, not a structure field. The ordered product asks only for `One`
and `Mul` — its bracketing is fixed, so neither associativity nor a unit law enters — and so is
available now.

The block map is `heckeTGeneratorRecGamma0 N` applied directly, with no primality guard. That
is exactly what `Diagonal/PrimePower.lean` bought by dropping `Nat.Prime p` from the recurrence:
the family is total in `p`, so it *is* a block map, and the composite needs no `dite` over
primality and no junk branch to reason around. The primality of `n.minFac` still does all the
mathematical work — it is what `heckeTCompositeGamma0_prime_pow` runs on — but it enters as a
hypothesis of the lemmas rather than as a guard inside the definition.

## The two grades of commutativity

The *per-prime* product formula is not proved here: it is `heckeTGeneratorRecGamma0_mul`, in
`Diagonal/PrimePower.lean`, a statement about the recurrence family with no assembly in it. This
file consumes it, and the two assembled results it proves ask for different things.

Coprime multiplicativity `T_{mn} = T_m · T_n` asks only that a block of `n` commute with the
blocks of `m` at larger primes — the hypothesis `TauCeti.Nat.primePowerProd_mul_of_coprime`
carries in place of a `CommMonoid` instance — so it is proved in the ambient `Semiring` its
neighbours use, with the obligations discharged pointwise from
`HeckeCosetModule.mul_comm_of_antiInvolution`.

The divisor table asks for more: `TauCeti.Nat.primePowerProd_mul_eq_sum_divisors_gcd` is stated
over a `CommRing`, so commutativity is needed as a *structure* rather than pointwise. It enters
through the private `commRingHeckeRingGamma0`, which adds `mul_comm` to the ambient `Ring`
instance; the ring structure is therefore the ambient one by construction, and only the proof of
`heckeTCompositeGamma0_mul` ever sees it.

## Main definitions

* `HeckeRing.GL2.heckeTCompositeGamma0`: the composite element assembled over the prime
  factorisation of `n`.
* `HeckeRing.GL2.heckeTScalarCompositeGamma0`: the composite scalar `∏_p S_p ^ v_p(n)`,
  assembled by the same ordered product. It is the `S_d` indexing the divisor table.

## Main results

* `HeckeRing.GL2.heckeTCompositeGamma0_prime_pow`: on a prime power the composite is the
  recurrence family, with no positivity hypothesis.
* `HeckeRing.GL2.heckeTCompositeGamma0_of_one_lt`: the peeling step, as a rewriting rule.
* `HeckeRing.GL2.heckeTCompositeGamma0_prime_pow_of_not_coprime`: at a prime sharing a factor
  with the level the composite degenerates to a power of the generator.
* `HeckeRing.GL2.heckeTCompositeGamma0_mul_of_coprime`: the composite is multiplicative on
  coprime arguments, `T_{mn} = T_m · T_n`.
* `HeckeRing.GL2.heckeTCompositeGamma0_mul`: **the global multiplication table**
  `T_m · T_n = ∑_{d ∣ gcd m n} d • (S_d · T_{mn/d²})`, for nonzero `m` and `n`. It subsumes the
  coprime case, where the gcd is `1` and the sum collapses to its `d = 1` term.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.3 — the multiplicative assembly
  `T_n = ∏_p T_{p^{v_p(n)}}` this file transcribes to the ring.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3 — Theorem 3.24(3), the multiplication table `heckeTCompositeGamma0_mul` states at level
  `Γ₀(N)`.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
  `projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`,
  declarations `heckeRingDn`, `heckeRingDn_ppow`, `heckeRingDn_peel`,
  `heckeRingDn_mul_coprime` and `heckeRingDn_mul` (lines 604-612, the divisor table).
  The source guards its block map with
  `if hp : Nat.Prime p then … else 1` because its prime-power family demands a primality
  proof; this file's does not, so the guard is dropped and
  `heckeTCompositeGamma0_prime_pow` loses the source's `0 < v` hypothesis with it. The source's
  peeling combinator `peelProd` is generalised out of the Hecke namespace into
  `TauCeti.Nat.primePowerProd`, where it belongs — it is combinatorics about `Nat.minFac`, with
  no Hecke content. For coprime multiplicativity the source installs a `CommRing` instance on
  the Hecke ring and calls its `CommMonoid`-level peeling lemma; here
  `TauCeti.Nat.primePowerProd_mul_of_coprime` asks instead for the commutations it actually
  uses, so no instance is swapped in and the obligations are discharged from
  `HeckeCosetModule.mul_comm_of_antiInvolution` directly.
-/

public section

open Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable (N : ℕ) [NeZero N]

/-- The composite element of the `Γ₀(N)` Hecke ring attached to `n`: the product of the
prime-power blocks `heckeTGeneratorRecGamma0 N p (n.factorization p)` over the primes `p ∣ n`,
taken least prime first. At a prime `p` this is the generator `T_p`, at a prime power `p ^ v`
the `v`-th term of the Diamond–Shurman recurrence, and at `1` — as at the junk input `0` — the
identity.

The ordering is an artefact of the weakened typeclass, not of the mathematics: once the Hecke
ring is known to be commutative the factors commute and the product is
`n.factorization.prod (heckeTGeneratorRecGamma0 N)` by
`TauCeti.Nat.primePowerProd_eq_factorization_prod`. -/
noncomputable def heckeTCompositeGamma0 (n : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  TauCeti.Nat.primePowerProd (heckeTGeneratorRecGamma0 N) n

/-- **The defining equation of the composite**: it *is* the ordered product of the recurrence
family over the factorisation. The body is sealed, so without this the
`TauCeti.Nat.primePowerProd` API — in particular the multiplicativity that arrives with
commutativity — is unreachable for it. -/
theorem heckeTCompositeGamma0_def (n : ℕ) :
    heckeTCompositeGamma0 N n = TauCeti.Nat.primePowerProd (heckeTGeneratorRecGamma0 N) n := (rfl)

/-- The junk input: `0` has no factorisation, and the empty product is the identity. -/
@[simp]
theorem heckeTCompositeGamma0_zero : heckeTCompositeGamma0 N 0 = 1 := by
  simpa only [heckeTCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_zero (heckeTGeneratorRecGamma0 N)

/-- `T₁ = 1`: the empty product over the empty factorisation. -/
@[simp]
theorem heckeTCompositeGamma0_one : heckeTCompositeGamma0 N 1 = 1 := by
  simpa only [heckeTCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_one (heckeTGeneratorRecGamma0 N)

/-- **The peeling step**: for `1 < n` the composite splits off the block at the least prime
factor of `n`, carrying its whole multiplicity. -/
theorem heckeTCompositeGamma0_of_one_lt {n : ℕ} (hn : 1 < n) : heckeTCompositeGamma0 N n =
    heckeTGeneratorRecGamma0 N n.minFac (n.factorization n.minFac) *
      heckeTCompositeGamma0 N (n / n.minFac ^ n.factorization n.minFac) := by
  simpa only [heckeTCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_of_one_lt (heckeTGeneratorRecGamma0 N) hn

/-- **On a prime power the composite is the recurrence family**: `T_{p^v}` assembled is
`T_{p^v}` generated.

No positivity is asked of `v`, unlike the general `TauCeti.Nat.primePowerProd_prime_pow`: at
`v = 0` both sides are the identity, the left by `heckeTCompositeGamma0_one` and the right by
`heckeTGeneratorRecGamma0_zero`. That the two junk conventions agree is what lets every
consumer below drop the hypothesis. -/
@[simp]
theorem heckeTCompositeGamma0_prime_pow {p : ℕ} (hp : p.Prime) (v : ℕ) :
    heckeTCompositeGamma0 N (p ^ v) = heckeTGeneratorRecGamma0 N p v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · simpa only [heckeTCompositeGamma0_def] using
      TauCeti.Nat.primePowerProd_prime_pow (heckeTGeneratorRecGamma0 N) hp hv

/-- At a prime the composite is the generator: `T_p` assembled is `T_p`. This is
`TauCeti.Nat.primePowerProd_prime` read through the definition. Marked `@[simp]` alongside
`heckeTCompositeGamma0_prime_pow`, which cannot fire here: a bare prime is not syntactically a
power, so without this lemma a prime input does not reduce to the generator. -/
@[simp]
theorem heckeTCompositeGamma0_prime {p : ℕ} (hp : p.Prime) :
    heckeTCompositeGamma0 N p = heckeTGeneratorGamma0 N p := by
  rw [heckeTCompositeGamma0_def, TauCeti.Nat.primePowerProd_prime _ hp,
    heckeTGeneratorRecGamma0_one]

/-- When `p` shares a factor with the level the scalar term of the recurrence vanishes and the
composite degenerates to a power of the generator: `T_{p^v} = T_p^v`. This is the bad-prime
half of the classical statement, and it is unconditional in `v`. -/
theorem heckeTCompositeGamma0_prime_pow_of_not_coprime {p : ℕ} (hp : p.Prime)
    (hpN : ¬Nat.Coprime p N) (v : ℕ) :
    heckeTCompositeGamma0 N (p ^ v) = heckeTGeneratorGamma0 N p ^ v := by
  rw [heckeTCompositeGamma0_prime_pow N hp v,
    heckeTGeneratorRecGamma0_eq_generator_pow_of_not_coprime N hpN]

/-- **Coprime multiplicativity**: `T_{mn} = T_m · T_n` when `m` and `n` share no prime factor.

The classical multiplicative relation among the `Γ₀(N)` Hecke operators, at the level of the
Hecke ring. Together with `heckeTCompositeGamma0_prime_pow`, which identifies the composite on
a prime power with the Diamond–Shurman recurrence family, it determines `T_n` for every
*positive* `n` from the prime-power data: split `n` into its prime powers here, then evaluate
each factor there. The junk input `0` has no factorisation to split and is fixed separately by
`heckeTCompositeGamma0_zero`. No hypothesis relates `m` or `n` to the level — the bad primes
are already absorbed into the blocks. -/
theorem heckeTCompositeGamma0_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    heckeTCompositeGamma0 N (m * n) = heckeTCompositeGamma0 N m * heckeTCompositeGamma0 N n := by
  -- One application of `primePowerProd_mul_of_coprime`, not an induction: it already sorts the
  -- interleaved blocks of `m * n` into those of `m` followed by those of `n`, and asks back only
  -- that a block of `n` commute with the blocks of `m` at larger primes. The Atkin–Lehner
  -- anti-involution commutes *any* two elements of this ring, so the primes never enter and the
  -- hypothesis is discharged by a constant function. Reading commutativity off that lemma rather
  -- than installing `commSemiringHeckeRingGamma0` as a local instance keeps this statement in the
  -- ambient `Semiring` its neighbours use — the choice `GL2/Recurrence.lean` already makes for
  -- the centrality of the scalar operator.
  simpa only [heckeTCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_mul_of_coprime (heckeTGeneratorRecGamma0 N) hmn fun _ _ _ _ _ ↦
      HeckeCosetModule.mul_comm_of_antiInvolution ℤ (atkinLehnerAntiInvolution N)
        (atkinLehnerAntiInvolution_onHeckeCoset_eq_self N) _ _

/-! ### The composite scalar, and the global multiplication table -/

/-- The composite **scalar** attached to `n`: the blocks `S_p ^ vₚ(n)` multiplied over the primes
of `n`, least prime first, by the same ordered product that assembles `heckeTCompositeGamma0`.

This is the `S_d` that indexes the divisor sum in `heckeTCompositeGamma0_mul`. At a prime power
it is a power of the scalar operator, at `1` — as at the junk input `0` — the identity. Where `p`
shares a factor with the level `S_p = 0`, so `heckeTScalarCompositeGamma0 N n = 0` as soon as
`n` has such a prime to a positive power. -/
noncomputable def heckeTScalarCompositeGamma0 (n : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  TauCeti.Nat.primePowerProd (fun p v ↦ heckeTScalarGamma0 N p ^ v) n

/-- **The defining equation of the composite scalar.** As for `heckeTCompositeGamma0_def`, the
body is sealed, so this is what reaches the `TauCeti.Nat.primePowerProd` API. -/
theorem heckeTScalarCompositeGamma0_def (n : ℕ) :
    heckeTScalarCompositeGamma0 N n =
      TauCeti.Nat.primePowerProd (fun p v ↦ heckeTScalarGamma0 N p ^ v) n := (rfl)

/-- The junk input: `0` has no factorisation, and the empty product is the identity. -/
@[simp]
theorem heckeTScalarCompositeGamma0_zero : heckeTScalarCompositeGamma0 N 0 = 1 := by
  simpa only [heckeTScalarCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_zero (fun p v ↦ heckeTScalarGamma0 N p ^ v)

/-- `S₁ = 1`: the empty product over the empty factorisation. -/
@[simp]
theorem heckeTScalarCompositeGamma0_one : heckeTScalarCompositeGamma0 N 1 = 1 := by
  simpa only [heckeTScalarCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_one (fun p v ↦ heckeTScalarGamma0 N p ^ v)

/-- **On a prime power the composite scalar is a power of the scalar operator.**

As with `heckeTCompositeGamma0_prime_pow` no positivity is asked of `v`: at `v = 0` both sides
are the identity, the left by `heckeTScalarCompositeGamma0_one` and the right by `pow_zero`. -/
@[simp]
theorem heckeTScalarCompositeGamma0_prime_pow {p : ℕ} (hp : p.Prime) (v : ℕ) :
    heckeTScalarCompositeGamma0 N (p ^ v) = heckeTScalarGamma0 N p ^ v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · simpa only [heckeTScalarCompositeGamma0_def] using
      TauCeti.Nat.primePowerProd_prime_pow (fun p v ↦ heckeTScalarGamma0 N p ^ v) hp hv

/-- The `Γ₀(N)` Hecke ring over `ℤ` as a *commutative* ring.

`TauCeti.Nat.primePowerProd_mul_eq_sum_divisors_gcd` is stated over a `CommRing`, so the table
below needs commutativity as a structure rather than as the pointwise
`HeckeCosetModule.mul_comm_of_antiInvolution` the neighbouring proofs quote. This adds `mul_comm`
to the *ambient* `Ring` instance rather than extending `commSemiringHeckeRingGamma0`, so its ring
structure is the ambient one by construction and no diamond is introduced: the statement of
`heckeTCompositeGamma0_mul` is in the ambient algebra and only its proof sees this.

Private and local for the same reason `commSemiringHeckeRingGamma0` is not an instance — the
anti-involution is data. -/
@[instance_reducible]
private noncomputable def commRingHeckeRingGamma0 :
    CommRing (𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ) :=
  { inferInstanceAs (Ring (𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ)) with
    mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution ℤ (atkinLehnerAntiInvolution N)
      (atkinLehnerAntiInvolution_onHeckeCoset_eq_self N) }

/-- **Shimura, Theorem 3.24(3)** at level `Γ₀(N)`, in full — the global multiplication table:

`T_m · T_n = ∑_{d ∣ gcd m n} d • (S_d · T_{mn/d²})`.

This is the composite counterpart of `heckeTGeneratorRecGamma0_mul`, which is the same identity
one prime at a time, and it subsumes `heckeTCompositeGamma0_mul_of_coprime`: when `m` and `n` are
coprime the gcd is `1`, the sum collapses to its `d = 1` term, and `S₁ = 1` leaves `T_m · T_n`.

Both arguments must be nonzero. `heckeTCompositeGamma0` sends `0` to the empty product `1` and
`gcd 0 0 = 0` has no divisors, so at `m = n = 0` the left side is `1` and the right an empty sum.

Together with `heckeTCompositeGamma0_prime_pow` this determines every product of two composite
elements from the prime-power data, which is what makes the `T_n` span a ring over a
factorisation. -/
theorem heckeTCompositeGamma0_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    heckeTCompositeGamma0 N m * heckeTCompositeGamma0 N n =
      ∑ d ∈ (Nat.gcd m n).divisors, (d : ℤ) •
        (heckeTScalarCompositeGamma0 N d * heckeTCompositeGamma0 N (m * n / d ^ 2)) := by
  letI := commRingHeckeRingGamma0 N
  simp only [heckeTCompositeGamma0_def, heckeTScalarCompositeGamma0_def]
  refine TauCeti.Nat.primePowerProd_mul_eq_sum_divisors_gcd _ _ (fun p hp r s hrs ↦ ?_) hm hn
  -- The per-prime table is `heckeTGeneratorRecGamma0_mul`; all that is needed is to read the
  -- assembled products at prime powers back as the blocks they are assembled from.
  have hD : ∀ v : ℕ, TauCeti.Nat.primePowerProd (heckeTGeneratorRecGamma0 N) (p ^ v) =
      heckeTGeneratorRecGamma0 N p v := fun v ↦
    (heckeTCompositeGamma0_def N (p ^ v)).symm.trans (heckeTCompositeGamma0_prime_pow N hp v)
  have hS : ∀ v : ℕ,
      TauCeti.Nat.primePowerProd (fun q w ↦ heckeTScalarGamma0 N q ^ w) (p ^ v) =
        heckeTScalarGamma0 N p ^ v := fun v ↦
    (heckeTScalarCompositeGamma0_def N (p ^ v)).symm.trans
      (heckeTScalarCompositeGamma0_prime_pow N hp v)
  simp only [hD, hS]
  exact heckeTGeneratorRecGamma0_mul N hrs

end HeckeRing.GL2
