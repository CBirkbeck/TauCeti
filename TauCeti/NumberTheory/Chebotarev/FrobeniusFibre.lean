/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Equipotent Frobenius fibres

For a finite Galois extension of number fields and a prime `𝔭` of the base, the primes
of the top field above `𝔭` are sorted by their arithmetic Frobenius. This file records
that conjugate Frobenius values sort out equally often: the fibre over `σ` and the fibre
over any conjugate `σ'` have the same cardinality.

This is the "distributed evenly" step of Chebotarev's density theorem: it is what lets a
count over a whole conjugacy class be recovered from the count at a single representative.
The bijection is conjugation by a witnessing element, via Mathlib's `IsArithFrobAt.conj`.

## Main results

* `NumberField.Chebotarev.frobeniusFibre_card_eq_of_isConj` — conjugate Frobenius elements
  have equipotent fibres above a fixed prime of the base.

## Implementation notes

The source states this with an unramifiedness hypothesis on `𝔭`, but never uses it: the
conjugation bijection is available at every prime. It is dropped here, which strengthens
the statement and keeps the argument list free of an unused binder.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (p. 143).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix.
-/

public section

open scoped NumberField Pointwise

namespace NumberField.Chebotarev

/-- **Equipotent Frobenius fibres.** For `IsConj σ σ'`, conjugating by a witnessing element
is a bijection between the primes above `𝔭` whose arithmetic Frobenius is `σ` and those
whose arithmetic Frobenius is `σ'`, so the two fibres have equal cardinality. -/
theorem frobeniusFibre_card_eq_of_isConj (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (σ σ' : L ≃ₐ[K] L) (hc : IsConj σ σ') :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ 𝔓}
      = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ' 𝔓} := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm c) fun 𝔓 ↦ ?_)
  simp only [MulAction.toPerm_apply]
  constructor
  · rintro ⟨hp, hP, hne, hfrob⟩
    have := hp
    have := hP
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · rw [← Ideal.smul_bot c]
      exact (MulAction.injective c).ne hne
    · exact hc ▸ hfrob.conj c
  · rintro ⟨hp, hP, hne, hfrob⟩
    have := hp
    have := hP
    have hsmul : c⁻¹ • (c • 𝔓) = 𝔓 := inv_smul_smul c 𝔓
    have hp' : 𝔓.IsPrime := hsmul ▸ (inferInstance : (c⁻¹ • (c • 𝔓)).IsPrime)
    have hP' : 𝔓.LiesOver 𝔭 := hsmul ▸ (inferInstance : (c⁻¹ • (c • 𝔓)).LiesOver 𝔭)
    have hne' : 𝔓 ≠ ⊥ := by
      rw [← hsmul, ← Ideal.smul_bot c⁻¹]
      exact (MulAction.injective c⁻¹).ne hne
    refine ⟨hp', hP', hne', ?_⟩
    have hconj := hfrob.conj c⁻¹
    rwa [hsmul, ← hc, show c⁻¹ * (c * σ * c⁻¹) * c⁻¹⁻¹ = σ by group] at hconj

end NumberField.Chebotarev
