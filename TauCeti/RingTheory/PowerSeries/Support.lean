/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Power series supported on multiples of `d`

A power series is *supported on multiples of `d`* when every coefficient at an index not
divisible by `d` vanishes. The condition is preserved by the module operations, so the series
satisfying it form a submodule, and everything the substitution `q ↦ q ^ d`
(`PowerSeries.expand`) produces satisfies it.

**Only that one inclusion is proved here.** The converse — that every supported series is such a
substitution — is not stated below, and nothing downstream needs it: the modular-form
applications only ever need to know that a level-raise *is* supported.

Nothing here mentions a modular form: the predicate is about power series over a semiring, and
the modular-form consequences live in
`TauCeti/NumberTheory/ModularForms/Degeneracy.lean` and
`TauCeti/NumberTheory/ModularForms/Newforms/QSupport.lean`, the latter obtaining its submodule of
cusp forms by pulling `PowerSeries.supportedOnDvdSubmodule` back along the `q`-expansion.

## Main definitions

* `PowerSeries.IsSupportedOnDvd`: the support condition on a power series.
* `PowerSeries.supportedOnDvdSubmodule`: the same condition bundled as a submodule.

## Main results

* `PowerSeries.IsSupportedOnDvd.add`, `.smul`, `.neg`, `.sub`: the condition is preserved by the
  module operations, and `.one`, `.mul` by the ring ones.
* `PowerSeries.isSupportedOnDvd_expand` and
  `PowerSeries.range_expand_le_supportedOnDvdSubmodule`: the substitution `q ↦ q ^ d` lands in the
  supported series, in predicate and in submodule form — a containment, not an equality. This is
  the only source of supported series that the modular-form applications use, so every
  `q ↦ q ^ d` statement about a `q`-expansion reduces to it.

## Typeclass assumptions

Each is the weakest Mathlib admits, which is worth recording because the statements look as though
they should ask for less:

* the predicate, and every lemma mentioning a coefficient, needs `[Semiring R]`, because Mathlib's
  only coefficient accessor is the bundled linear map `PowerSeries.coeff n : R⟦X⟧ →ₗ[R] R`
  (`LinearMap.proj n`, declared under `variable [Semiring R]`). There is no unbundled reader, so
  the condition cannot be stated at `[Zero R]`;
* `.neg` and `.sub` need `[Ring R]`, because `Neg R⟦X⟧` is available only then;
* `.smul` needs `[Semiring S] [Module S R]`, because Mathlib's only scalar action on power series
  is `Module R (MvPowerSeries σ A)` for `[Semiring R] [AddCommMonoid A] [Module R A]`;
* the two `expand` lemmas need `[CommRing R]`, because `PowerSeries.expand` is an `R`-algebra
  homomorphism defined only there.

## Provenance

`IsSupportedOnDvd` and its closure lemmas `zero`, `add`, `smul`, `neg`, `sub`, `one` are adapted
from the AINTLIB `LeanModularForms` project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/AtkinLehner.lean`. The source states them
over `ℂ`, inside its `HeckeRing.GL2.AtkinLehner` namespace; here they are about power series over
a semiring — `neg` and `sub` over a ring, `smul` over a module — and are placed in the
`PowerSeries` namespace under `RingTheory/` accordingly, since nothing in them mentions a modular
form. The modular-form consequences the source draws from them are in
`TauCeti/NumberTheory/ModularForms/Degeneracy.lean`.

The `expand` bridge has no counterpart in the source, which reaches the same conclusions by a
coefficient computation at each use site.
-/

public section

namespace PowerSeries

/-- A power series is **supported on multiples of `d`** when its coefficient at every index
not divisible by `d` vanishes. -/
def IsSupportedOnDvd {R : Type*} [Semiring R] (d : ℕ) (P : PowerSeries R) : Prop :=
  ∀ n : ℕ, ¬ d ∣ n → P.coeff n = 0

/-- `IsSupportedOnDvd` restated as an `Iff`, so the defining condition is available to `rw`
without unfolding the definition. -/
theorem isSupportedOnDvd_iff {R : Type*} [Semiring R] {d : ℕ} {P : PowerSeries R} :
    IsSupportedOnDvd d P ↔ ∀ n : ℕ, ¬ d ∣ n → P.coeff n = 0 := (Iff.rfl)

namespace IsSupportedOnDvd

variable {R S : Type*} {d : ℕ} {P Q : PowerSeries R}

@[simp]
theorem zero [Semiring R] (d : ℕ) : IsSupportedOnDvd d (0 : PowerSeries R) := fun _ _ ↦ by simp

theorem add [Semiring R] (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P + Q) := fun n hn ↦ by
  rw [map_add, hP n hn, hQ n hn, zero_add]

theorem smul [Semiring R] [Semiring S] [Module S R] (c : S) (hP : IsSupportedOnDvd d P) :
    IsSupportedOnDvd d (c • P) := fun n hn ↦ by
  simp [hP n hn]

theorem neg [Ring R] (hP : IsSupportedOnDvd d P) : IsSupportedOnDvd d (-P) := fun n hn ↦ by
  rw [map_neg, hP n hn, neg_zero]

theorem sub [Ring R] (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P - Q) := sub_eq_add_neg P Q ▸ hP.add hQ.neg

/-- The constant power series `1` is supported on multiples of any `d`: its only nonzero
coefficient sits at `0`, which every `d` divides. -/
@[simp]
theorem one [Semiring R] (d : ℕ) : IsSupportedOnDvd d (1 : PowerSeries R) := fun n hn ↦ by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd (dvd_zero d) hn
  · simp [PowerSeries.coeff_one, hpos.ne']

/-- **The condition is closed under multiplication.** In a coefficient of `P * Q` at an index
`n` not divisible by `d`, each term `aᵢ · b_j` with `i + j = n` has one of its two factors at an
index away from the multiples of `d`: if `d ∣ i` then `d ∤ j`, since otherwise `d ∣ n`.

Both hypotheses are needed. One-sidedness fails: over any semiring, `1` is supported on multiples
of `2` while `1 * X = X` is not. -/
theorem mul [Semiring R] (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P * Q) := fun n hn ↦ by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases hi : d ∣ x.1
  · rw [hQ x.2 fun hj ↦ hn (hx ▸ hi.add hj), mul_zero]
  · rw [hP x.1 hi, zero_mul]

end IsSupportedOnDvd

/-- The submodule of power series supported on multiples of `d`. This is the bundled form of
`IsSupportedOnDvd`; its closure proofs are exactly the lemmas above. -/
def supportedOnDvdSubmodule (R : Type*) [Semiring R] (d : ℕ) : Submodule R (PowerSeries R) where
  carrier := {P | IsSupportedOnDvd d P}
  zero_mem' := IsSupportedOnDvd.zero d
  add_mem' hP hQ := hP.add hQ
  smul_mem' c _ hP := hP.smul c

@[simp]
theorem mem_supportedOnDvdSubmodule {R : Type*} [Semiring R] {d : ℕ} {P : PowerSeries R} :
    P ∈ supportedOnDvdSubmodule R d ↔ IsSupportedOnDvd d P := (Iff.rfl)

section Expand

variable {R : Type*} [CommRing R] {d : ℕ}

/-- **Substituting `q ↦ q ^ d` lands in the supported series.** Every coefficient of
`PowerSeries.expand d` sits at a multiple of `d`, which is the defining condition. This is the
bridge that turns a `q ↦ q ^ d` description of a series into the support condition, so the
support statements downstream never repeat the coefficient computation. -/
theorem isSupportedOnDvd_expand (hd : d ≠ 0) (P : PowerSeries R) :
    IsSupportedOnDvd d (P.expand d hd) := fun _ hn ↦ coeff_expand_of_not_dvd d hd P hn

/-- **The range of `PowerSeries.expand d` lies in the supported submodule**, the bundled form of
`PowerSeries.isSupportedOnDvd_expand`. `expand` is an `AlgHom`, so the range is taken of its
underlying linear map. -/
theorem range_expand_le_supportedOnDvdSubmodule (hd : d ≠ 0) :
    LinearMap.range (expand (R := R) d hd).toLinearMap ≤ supportedOnDvdSubmodule R d := by
  rintro _ ⟨P, rfl⟩
  exact isSupportedOnDvd_expand hd P

end Expand

end PowerSeries

end
