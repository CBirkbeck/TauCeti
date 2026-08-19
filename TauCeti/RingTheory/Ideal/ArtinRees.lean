/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# Lifting through a surjection with control on the `I`-adic filtration

Mathlib's Artin–Rees lemma, `Ideal.exists_pow_inf_eq_pow_smul`, compares the `I`-adic filtration
of a module with the filtration it induces on a submodule. This file draws the lifting consequence
that the adic theory uses.

Fix a submodule `K` of a finite module `M` over a noetherian ring, and a surjection `φ` onto `K`
from any module `P`. Then **one shift `k₀` works at every depth**: an element of `K` that lies
`k₀` steps deeper than `m` in the *ambient* filtration of `M` is the image under `φ` of something
at depth `m` in `P`.

The shift is what makes the statement useful and what makes it non-trivial. Membership in
`I ^ n • ⊤` is measured in `M`, while a lift is constrained by the filtration `K` inherits, and
those two differ; Artin–Rees is exactly the input that bounds the discrepancy by a constant
independent of `n`. Without the shift the statement is false in general.

Nothing here is topological or adic-space-specific — it is filtration algebra over an arbitrary
commutative noetherian ring — so it sits beside Mathlib's own Artin–Rees material rather than in
the Huber development that consumes it.

## Main results

* `TauCeti.ArtinRees.exists_controlled_lift`: a surjection onto a submodule admits lifts with
  control on the `I`-adic filtration, up to a shift depending only on `I` and the submodule.

## Provenance

Adapted from AINTLIB's `ArtinRees.controlled_lift`, branch `dev/adic-spaces`, commit `37bbdaeb`,
Apache-2.0, Chris Birkbeck, `projects/AdicSpaces/Adic spaces/ArtinReesConvergence.lean`, whose
reference is Wedhorn Lemma 8.31. Two generalisations:

* the source fixes the ambient module to `Fin l → R` and the source of the surjection to
  `Fin k → R`, presenting the map as `∑ j, c j • s j` for a chosen spanning family; here the
  ambient module, the source and the map are arbitrary, since the proof uses only surjectivity.
  The source's `surjMap` and its two lemmas are consequently dropped — that map is Mathlib's
  `Fintype.linearCombination`, and the image computation is `Submodule.map_smul''` composed with
  `Submodule.map_top`;
* the source takes the Artin–Rees conclusion as a hypothesis `hAR` together with the constant
  `k₀`; here both come from `Ideal.exists_pow_inf_eq_pow_smul`, so no caller has to supply them.

One declaration is not ported: the source's `pi_smul_top_component`, which has no consumer.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.31.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/ArtinReesConvergence.lean`.
-/

public section

namespace TauCeti.ArtinRees

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **Artin–Rees controlled lift.** For an ideal `I` and a submodule `K` of a finite module over a
noetherian ring there is a shift `k₀`, independent of the depth, such that every `v : K` whose
image in `M` lies in `I ^ (m + k₀) • ⊤` has a `φ`-preimage in `I ^ m • ⊤`. -/
theorem exists_controlled_lift [IsNoetherianRing R] [Module.Finite R M] (I : Ideal R)
    (K : Submodule R M) {P : Type*} [AddCommGroup P] [Module R P] (φ : P →ₗ[R] K)
    (hφ : Function.Surjective φ) :
    ∃ k₀ : ℕ, ∀ (m : ℕ) (v : K), (v : M) ∈ (I ^ (m + k₀) • ⊤ : Submodule R M) →
      ∃ c ∈ (I ^ m • ⊤ : Submodule R P), φ c = v := by
  obtain ⟨k₀, hAR⟩ := I.exists_pow_inf_eq_pow_smul K
  refine ⟨k₀, fun m v hv ↦ ?_⟩
  -- Artin–Rees turns ambient depth `m + k₀` into depth `m` for the filtration induced on `K`
  have hv_inf : (v : M) ∈ I ^ (m + k₀) • ⊤ ⊓ K := ⟨hv, v.prop⟩
  rw [hAR (m + k₀) (Nat.le_add_left k₀ m), Nat.add_sub_cancel] at hv_inf
  have hv_smul_K : (v : M) ∈ I ^ m • K := (Submodule.smul_mono le_rfl inf_le_right) hv_inf
  have hv_top : v ∈ (I ^ m • ⊤ : Submodule R K) :=
    (Submodule.mem_smul_top_iff (I ^ m) K v).mpr hv_smul_K
  -- a surjection carries `I ^ m • ⊤` onto `I ^ m • ⊤`, so the lift can be taken at depth `m`
  have hmap : (I ^ m • ⊤ : Submodule R P).map φ = (I ^ m • ⊤ : Submodule R K) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hφ]
  rw [← hmap] at hv_top
  exact Submodule.mem_map.mp hv_top

end TauCeti.ArtinRees

end
