/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Localization.Away
public import TauCeti.Topology.Algebra.TopologicallyNilpotent

/-!
# Localising an open subring at a topologically nilpotent element

Let `B` be an **open** subring of a topological ring `A`, and let `s : B` be topologically
nilpotent in `A`. Inverting `s` on both sides does not distinguish the two rings: the induced map
`B_s → A_s` is a ring isomorphism.

The point is that `B` is open, so a topologically nilpotent `s` absorbs every element of `A` into
`B` after enough multiplications. Passing to `B_s` makes that absorption invertible, which is
exactly what surjectivity needs. Injectivity is not topological at all and lives one file down, in
`RingTheory/Localization/Away.lean`, as `TauCeti.Localization.awayMap_subtype_injective`.

## Implementation notes

Surjectivity goes through the Mathlib criterion rather than through elements of the localisations:
`IsLocalization.Away.map_surjective_iff` reduces it to "every `a : A` is `sᵐ` times the image of
something in `B`", which is `exists_mul_pow_mem_of_isTopologicallyNilpotent` verbatim, up to
commuting the product.

Only `ContinuousMul` is assumed, matching the absorption lemma: continuity of addition, a
nonarchimedean neighbourhood basis and any Huber structure are all irrelevant here.

## Source

Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), the localisation step inside the proof of Lemma
7.44(1). Only that step is formalised here — the spectral half of 7.44(1), the homeomorphism
between the complements of the two closed subsets, is **not** proved in this file.

## Main results

* `TauCeti.Localization.awayMap_subtype_surjective_of_isTopologicallyNilpotent`: the induced map on
  localisations is surjective when the subring is open and `s` is topologically nilpotent.
* `TauCeti.Localization.awayRingEquivOfIsTopologicallyNilpotent`: the resulting isomorphism
  `B_s ≃+* A_s`.
-/

public section

namespace TauCeti.Localization

variable {A : Type*} [CommRing A] [TopologicalSpace A] [ContinuousMul A]
variable {B : Subring A} {s : B}
variable (Bs As : Type*) [CommRing Bs] [CommRing As]
  [Algebra B Bs] [IsLocalization.Away s Bs]
  [Algebra A As] [IsLocalization.Away (B.subtype s) As]

/-- **The localisation of an open subring surjects onto the localisation of the ring.** Given
`a : A`, the topologically nilpotent `s` absorbs it into the open subring `B` after some number of
multiplications, and inverting `s` undoes them. -/
theorem awayMap_subtype_surjective_of_isTopologicallyNilpotent (hB : IsOpen (B : Set A))
    (hs : IsTopologicallyNilpotent (s : A)) :
    Function.Surjective (IsLocalization.Away.map Bs As B.subtype s) := by
  rw [IsLocalization.Away.map_surjective_iff]
  intro a
  obtain ⟨n, hn⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent hs hB a
  exact ⟨⟨a * (s : A) ^ n, hn⟩, n, mul_comm a ((s : A) ^ n)⟩

/-- **Inverting a topologically nilpotent element does not see an open subring.** For `B` an open
subring of `A` and `s : B` topologically nilpotent in `A`, the induced map `B_s → A_s` is a ring
isomorphism: injective for any subring, surjective because `s` absorbs into the open `B`. -/
noncomputable def awayRingEquivOfIsTopologicallyNilpotent (hB : IsOpen (B : Set A))
    (hs : IsTopologicallyNilpotent (s : A)) : Bs ≃+* As :=
  RingEquiv.ofBijective _ ⟨awayMap_subtype_injective Bs As,
    awayMap_subtype_surjective_of_isTopologicallyNilpotent Bs As hB hs⟩

@[simp] theorem coe_awayRingEquivOfIsTopologicallyNilpotent (hB : IsOpen (B : Set A))
    (hs : IsTopologicallyNilpotent (s : A)) :
    ⇑(awayRingEquivOfIsTopologicallyNilpotent Bs As hB hs) =
      IsLocalization.Away.map Bs As B.subtype s :=
  -- `rfl` cannot see through `awayRingEquivOfIsTopologicallyNilpotent`: its body is not exposed
  -- outside this module, so the coercion is unfolded through `RingEquiv`'s own interface lemma.
  RingEquiv.coe_ofBijective _ _

end TauCeti.Localization

end
