/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.IntegralDomain

/-!
# Column orthogonality and Fourier inversion for finite commutative groups

For a finite commutative group `G` and a domain `M` with enough roots of unity, the characters
of `G` are the monoid homomorphisms `G →* Mˣ`. This file records the *column* orthogonality
relation — the one summed over the character group — and the Fourier-inversion statement it
supports.

## Main results

* `CommGroup.sum_char_apply_eq_zero_of_ne_one`: for `g ≠ 1`, the sum `∑ χ : G →* Mˣ, χ g`
  over all characters vanishes.
* `CommGroup.card_mul_eq_sum_of_sum_char_mul_eq_zero`: a function whose nontrivial character
  moments all vanish is recovered from its average.
* `CommGroup.eq_of_sum_char_mul_eq_zero`: over a characteristic-zero domain the same hypothesis
  forces the function to be constant.

## Row orthogonality is Mathlib's, and is deliberately not restated here

The companion *row* relation — for a nontrivial `χ : G →* Mˣ`, the sum `∑ g : G, χ g` over the
group vanishes — is already `sum_hom_units_eq_zero` in
`Mathlib/RingTheory/IntegralDomain.lean`, which states exactly that for an arbitrary monoid
homomorphism `G →* R` into a domain. Specialising it to a character is
`sum_hom_units_eq_zero ((Units.coeHom M).comp χ)`, i.e. the Mathlib lemma composed with the
unit coercion and nothing else, so no declaration for it is added. Callers wanting the row
relation should use the Mathlib lemma directly. (`MulChar.sum_eq_zero_of_ne_one` in
`Mathlib/NumberTheory/MulChar/Basic.lean` is the same content in the `MulChar` vocabulary,
stated over a finite ring rather than a finite group.)

The column relation genuinely is not in Mathlib in this generality: it appears only in the
`ZMod n` specialisation `DirichletCharacter.sum_characters_eq_zero`, in
`Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean`.

## References

Adapted from `CebotarevDensity/ForMathlib/CharacterOrthogonality.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The source file also
carries the row relation as `sum_char_self_eq_zero_of_ne_one`; that declaration is dropped here
in favour of Mathlib's `sum_hom_units_eq_zero`, as described above.
-/

@[expose] public section

namespace CommGroup

variable {G : Type*} [CommGroup G] {M : Type*} [CommRing M] [IsDomain M]

/-- **Character-column orthogonality** for a finite commutative group `G` valued in a domain `M`
with enough roots of unity: for `g ≠ 1`, the sum of `χ g` over all characters `χ : G →* Mˣ`
vanishes. -/
theorem sum_char_apply_eq_zero_of_ne_one [Finite G] [HasEnoughRootsOfUnity M (Monoid.exponent G)]
    [Fintype (G →* Mˣ)] {g : G} (hg : g ≠ 1) : ∑ χ : G →* Mˣ, (χ g : M) = 0 := by
  -- A specialisation of `sum_hom_units_eq_zero` on the dual group `G →* Mˣ` along the
  -- evaluation homomorphism `χ ↦ χ g`.
  obtain ⟨χ₀, hχ₀⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity G M hg
  exact sum_hom_units_eq_zero ((Units.coeHom M).comp (MonoidHom.eval g))
    fun h ↦ hχ₀ <| Units.val_eq_one.mp <| DFunLike.congr_fun h χ₀

variable [Fintype G] [HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- **Finite-abelian Fourier inversion.** If every nontrivial character moment of `f : G → M`
vanishes — `∑ s, χ s * f s = 0` for each `χ ≠ 1` — then `f` is recovered from its average: for
every `u`, `(#(G →* Mˣ)) * f u = ∑ s, f s`. -/
theorem card_mul_eq_sum_of_sum_char_mul_eq_zero [Fintype (G →* Mˣ)] (f : G → M)
    (hf : ∀ χ : G →* Mˣ, χ ≠ 1 → ∑ s : G, (χ s : M) * f s = 0) (u : G) :
    (Fintype.card (G →* Mˣ) : M) * f u = ∑ s : G, f s := by
  -- column orthogonality: every `s ≠ u` term of the double sum below vanishes
  calc (Fintype.card (G →* Mˣ) : M) * f u
      = ∑ s : G, ∑ χ : G →* Mˣ, (χ (u⁻¹ * s) : M) * f s := by
        rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ _) fun s _ hs ↦ by
          rw [← Finset.sum_mul, sum_char_apply_eq_zero_of_ne_one
            fun h ↦ hs (inv_mul_eq_one.mp h).symm, zero_mul]]
        simp
    _ = ∑ χ : G →* Mˣ, (χ u⁻¹ : M) * ∑ s : G, (χ s : M) * f s :=
        Finset.sum_comm.trans (by simp [Finset.mul_sum, mul_assoc])
    -- the hypothesis collapses the character sum to its principal term
    _ = ∑ s : G, f s :=
        (Finset.sum_eq_single_of_mem (1 : G →* Mˣ) (Finset.mem_univ _)
          fun χ _ hχ ↦ by rw [hf χ hχ, mul_zero]).trans (by simp)

/-- **Vanishing nontrivial Fourier coefficients force a constant.** Over a characteristic-zero
domain, if every nontrivial character moment of `f : G → M` vanishes (`∑ s, χ s * f s = 0` for
`χ ≠ 1`), then `f` takes the same value at every pair of points. -/
theorem eq_of_sum_char_mul_eq_zero [CharZero M] (f : G → M)
    (hf : ∀ χ : G →* Mˣ, χ ≠ 1 → ∑ s : G, (χ s : M) * f s = 0) (u u' : G) : f u = f u' := by
  -- Immediate from `card_mul_eq_sum_of_sum_char_mul_eq_zero` — both values equal the common
  -- average — after cancelling the nonzero dual cardinality.
  have : Fintype (G →* Mˣ) := Fintype.ofFinite _
  have h := card_mul_eq_sum_of_sum_char_mul_eq_zero f hf
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) <| (h u).trans (h u').symm

end CommGroup
