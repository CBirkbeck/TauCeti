/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Power series supported on multiples of `d`

A power series is *supported on multiples of `d`* when every coefficient at an index not
divisible by `d` vanishes. The condition is preserved by the module operations, so the series
satisfying it form a submodule.

Nothing here mentions a modular form: the predicate is about power series over a semiring, and
the modular-form consequences live in
`TauCeti/NumberTheory/ModularForms/Newforms/QSupport.lean`, which obtains its submodule of cusp
forms by pulling `supportedOnDvdSubmodule` back along the `q`-expansion.

## Main definitions

* `TauCeti.IsSupportedOnDvd`: the support condition on a power series.
* `TauCeti.supportedOnDvdSubmodule`: the same condition bundled as a submodule.

## Main results

* `TauCeti.IsSupportedOnDvd.add`, `.smul`, `.neg`, `.sub`: the condition is preserved by the
  module operations.

## Provenance

`IsSupportedOnDvd` and its closure lemmas `zero`, `add`, `smul`, `neg`, `sub`, `one` are adapted
from the AINTLIB `LeanModularForms` project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/AtkinLehner.lean`. The source states them
over `ℂ`, inside its `HeckeRing.GL2.AtkinLehner` namespace; here they are about power series over
a semiring — `neg` and `sub` over a ring, `smul` over a module — and are placed in `RingTheory/`
accordingly, since nothing in them mentions a modular form. The modular-form consequences the
source draws from them are in `TauCeti/NumberTheory/ModularForms/Newforms/QSupport.lean`.
-/

public section

namespace TauCeti

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

/-- The elimination form: a supported series has vanishing coefficients away from the
multiples of `d`. -/
theorem coeff_of_not_dvd [Semiring R] (hP : IsSupportedOnDvd d P) {n : ℕ} (hn : ¬ d ∣ n) :
    P.coeff n = 0 := hP n hn

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
theorem one [Semiring R] (d : ℕ) : IsSupportedOnDvd d (1 : PowerSeries R) := fun n hn ↦ by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd (dvd_zero d) hn
  · simp [PowerSeries.coeff_one, hpos.ne']

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

end TauCeti

end
