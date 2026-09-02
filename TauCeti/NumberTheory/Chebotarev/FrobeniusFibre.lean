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

private theorem exists_isArithFrobAt_smul {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] {𝔭 : Ideal (𝓞 K)} {σ τ c : L ≃ₐ[K] L}
    {𝔓 : Ideal (𝓞 L)} (hτ : c * σ * c⁻¹ = τ)
    (h : ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓) :
    ∃ (_ : (c • 𝔓).IsPrime) (_ : (c • 𝔓).LiesOver 𝔭) (_ : c • 𝔓 ≠ ⊥),
      IsArithFrobAt (𝓞 K) τ (c • 𝔓) := by
  obtain ⟨_, _, hne, hfrob⟩ := h
  refine ⟨inferInstance, inferInstance, ?_, hτ ▸ hfrob.conj c⟩
  simpa using (MulAction.injective c).ne hne

/-- **Equipotent Frobenius fibres.** For `IsConj σ σ'`, the nonzero primes above `𝔭` with
arithmetic Frobenius `σ` are equal in number to those with arithmetic Frobenius `σ'`. -/
theorem frobeniusFibre_card_eq_of_isConj (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (σ σ' : L ≃ₐ[K] L)
    (hc : IsConj σ σ') :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ 𝔓} =
      Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ' 𝔓} := by
  -- conjugating by a witnessing element `c` is the bijection between the two fibres
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm c) fun 𝔓 ↦ ?_)
  simp only [MulAction.toPerm_apply]
  refine ⟨exists_isArithFrobAt_smul rfl, fun h ↦ ?_⟩
  -- the reverse direction is the same transport along `c⁻¹`
  simpa using exists_isArithFrobAt_smul (c := c⁻¹) (τ := σ) (by group) h

end NumberField.Chebotarev
