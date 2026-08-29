/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Topology.Algebra.TopologicallyNilpotent

/-!
# Localising an open subring at a topologically nilpotent element

Let `B` be an **open** subring of a topological ring `A`, and let `s : B` be topologically
nilpotent in `A`. Inverting `s` on both sides does not distinguish the two rings: the induced map
`B_s → A_s` is a ring isomorphism.

The point is that `B` is open, so a topologically nilpotent `s` absorbs every element of `A` into
`B` after enough multiplications. Passing to `B_s` makes that absorption invertible, which is
exactly what surjectivity needs, while injectivity is free because `B → A` is injective to begin
with.

## Implementation notes

Both halves go through the Mathlib criteria rather than through elements of the localisations.
`IsLocalization.Away.map_injective_iff` reduces injectivity to "if `b` dies in `A` then some
`sⁿ * b` dies in `B`", which holds with `n = 0` since `Subring.subtype` is injective — no power of
`s` is needed. `IsLocalization.Away.map_surjective_iff` reduces surjectivity to "every `a : A` is
`sᵐ` times the image of something in `B`", which is `exists_mul_pow_mem_of_isTopologicallyNilpotent`
verbatim, up to commuting the product.

Only `ContinuousMul` is assumed, matching the absorption lemma: continuity of addition, a
nonarchimedean neighbourhood basis and any Huber structure are all irrelevant here.

## Source

Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), the localisation step inside the proof of Lemma
7.44(1). Only that step is formalised here — the spectral half of 7.44(1), the homeomorphism
between the complements of the two closed subsets, is **not** proved in this file.

## Main results

* `injective_awayMap_subtype`: the induced map on localisations is injective, for any subring.
* `surjective_awayMap_subtype_of_isTopologicallyNilpotent`: it is surjective when the subring is
  open and `s` is topologically nilpotent.
* `bijective_awayMap_subtype_of_isTopologicallyNilpotent`: hence bijective.
* `awayRingEquivOfIsTopologicallyNilpotent`: the isomorphism `B_s ≃+* A_s` it packages.
-/

public section

variable {A : Type*} [CommRing A]
variable {B : Subring A} {s : B}
variable (Bs As : Type*) [CommRing Bs] [CommRing As]
  [Algebra B Bs] [IsLocalization.Away s Bs]
  [Algebra A As] [IsLocalization.Away (B.subtype s) As]

/-- **The localisation of a subring injects into the localisation of the ring.** No topology and no
openness are needed: `B → A` is injective, so an element of `B` that dies in `A` is already zero,
and the criterion is met with the zeroth power of `s`. -/
theorem injective_awayMap_subtype :
    Function.Injective (IsLocalization.Away.map Bs As B.subtype s) := by
  rw [IsLocalization.Away.map_injective_iff]
  exact fun b hb ↦ ⟨0, by rw [pow_zero, one_mul]; exact Subtype.ext hb⟩

-- The topology enters only from here: it is what makes `s` absorb elements of `A` into `B`.
variable [TopologicalSpace A] [ContinuousMul A]

/-- **The localisation of an open subring surjects onto the localisation of the ring.** Given
`a : A`, the topologically nilpotent `s` absorbs it into the open subring `B` after some number of
multiplications, and inverting `s` undoes them. -/
theorem surjective_awayMap_subtype_of_isTopologicallyNilpotent (hB : IsOpen (B : Set A))
    (hs : IsTopologicallyNilpotent (s : A)) :
    Function.Surjective (IsLocalization.Away.map Bs As B.subtype s) := by
  rw [IsLocalization.Away.map_surjective_iff]
  intro a
  obtain ⟨n, hn⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent hs hB a
  exact ⟨⟨a * (s : A) ^ n, hn⟩, n, mul_comm a ((s : A) ^ n)⟩

/-- **Inverting a topologically nilpotent element does not see an open subring.** For `B` an open
subring of `A` and `s : B` topologically nilpotent in `A`, the induced map `B_s → A_s` is
bijective. -/
theorem bijective_awayMap_subtype_of_isTopologicallyNilpotent (hB : IsOpen (B : Set A))
    (hs : IsTopologicallyNilpotent (s : A)) :
    Function.Bijective (IsLocalization.Away.map Bs As B.subtype s) :=
  ⟨injective_awayMap_subtype Bs As,
    surjective_awayMap_subtype_of_isTopologicallyNilpotent Bs As hB hs⟩

/-- The isomorphism `B_s ≃+* A_s` of
`bijective_awayMap_subtype_of_isTopologicallyNilpotent`. -/
noncomputable def awayRingEquivOfIsTopologicallyNilpotent (hB : IsOpen (B : Set A))
    (hs : IsTopologicallyNilpotent (s : A)) : Bs ≃+* As :=
  RingEquiv.ofBijective _ (bijective_awayMap_subtype_of_isTopologicallyNilpotent Bs As hB hs)

@[simp] theorem coe_awayRingEquivOfIsTopologicallyNilpotent (hB : IsOpen (B : Set A))
    (hs : IsTopologicallyNilpotent (s : A)) :
    ⇑(awayRingEquivOfIsTopologicallyNilpotent Bs As hB hs) =
      IsLocalization.Away.map Bs As B.subtype s :=
  -- `rfl` cannot see through `awayRingEquivOfIsTopologicallyNilpotent`: its body is not exposed
  -- outside this module, so the coercion is unfolded through `RingEquiv`'s own interface lemma.
  RingEquiv.coe_ofBijective _ _

end
