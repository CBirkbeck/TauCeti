/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Basic

/-!
# Rescaling a presentation leaves the candidate ring of definition alone

A rational localisation is presented by a pair `(T, s)` — numerators and a denominator — and the
candidate ring of definition `D = A₀[t/s : t ∈ T]` is built from that presentation, not from the
subset it cuts out. Multiplying numerators *and* denominator by one common factor `u` is
therefore invisible to `D`: every generator `(u · t)/(u · s)` is the generator `t/s` it came from,
by `TauCeti.Localization.divBy_mul_mul_left`.

This is the first step of a change of presentation. Over a Tate ring one wants to replace `(T, s)`
by `(ϖ ^ i · T, ϖ ^ i · s)` for a pseudouniformiser `ϖ`, chosen so that the denominator becomes
topologically nilpotent
(`TauCeti.Huber.IsTateRing.exists_isTopologicallyNilpotent_pow_mul`); the rational subset is
unchanged because a unit rescaling does not move the ideal the presentation spans
(`Submodule.span_smul_eq_of_isUnit`), and the localisation is unchanged because `u * s` and `s` are
associated (`IsLocalization.Away.iff_of_associated`). What is recorded here is that the *ring of
definition* is unchanged too.

## Main results

* `TauCeti.Huber.PairOfDefinition.locSubring_eq_of_coe_eq_image_mul`: if the numerators of one
  presentation are the `u`-multiples of the numerators of another, and the denominators differ by
  the same `u`, the two presentations have the same `locSubring`.

## Implementation notes

The rescaled numerator set is taken as a `Finset` `T'` together with `(T' : Set A) = (u * ·) '' T`,
rather than as `T.image (u * ·)`. `Finset.image` would need `DecidableEq A`, which a Huber ring has
no reason to carry, and a caller building `T'` by any route can supply the set-level equation.

No unit hypothesis on `u` is needed. Only `[IsLocalization.Away (u * s) S]` is used, and in the
intended application that instance is exactly what being a unit supplies.
-/

public section

namespace TauCeti.Huber.PairOfDefinition

open TauCeti.Localization

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Rescaling numerators and denominator by a common factor does not change `D`.** Each
generator of one side is a generator of the other, by `divBy_mul_mul_left`. -/
theorem locSubring_eq_of_coe_eq_image_mul (P : PairOfDefinition A) (T T' : Finset A) (u s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    [IsLocalization.Away (u * s) S] (hT' : (T' : Set A) = (u * ·) '' (T : Set A)) :
    P.locSubring T' (u * s) S = P.locSubring T s S := by
  refine le_antisymm ((locSubring_le_iff P T' (u * s) S).mpr
    ⟨fun a ha ↦ algebraMap_mem_locSubring P T s S ha, fun t' ht' ↦ ?_⟩)
    ((locSubring_le_iff P T s S).mpr
      ⟨fun a ha ↦ algebraMap_mem_locSubring P T' (u * s) S ha, fun t ht ↦ ?_⟩)
  · obtain ⟨t, ht, rfl⟩ := hT' ▸ Finset.mem_coe.mpr ht'
    rw [divBy_mul_mul_left]
    exact divBy_mem_locSubring P T s S ht
  · rw [← divBy_mul_mul_left (u := u) t s]
    exact divBy_mem_locSubring P T' (u * s) S
      (Finset.mem_coe.mp (hT' ▸ Set.mem_image_of_mem _ (Finset.mem_coe.mpr ht)))

end TauCeti.Huber.PairOfDefinition

end
