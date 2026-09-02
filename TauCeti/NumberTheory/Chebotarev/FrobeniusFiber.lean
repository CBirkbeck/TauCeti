/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.NumberField.AutomorphismAction

/-!
# Equipotent Frobenius fibers

For an extension of number fields and a prime `𝔭` of the base, each `K`-automorphism `σ`
of `L` cuts out the set of primes above `𝔭` that admit `σ` as an arithmetic
Frobenius. These sets need not be disjoint: at a ramified prime several elements are a
Frobenius at once, so this is a family of fibers rather than a partition. This file records
that conjugate values are admitted equally often: the fiber over `σ` and the fiber over any
conjugate `σ'` have the same cardinality.

This is the "distributed evenly" step of Chebotarev's density theorem. At a prime unramified in
`L` the fibers do partition the primes above `𝔭`, and there this is exactly what lets a count
over a whole conjugacy class be recovered from the count at a single representative. That
consequence needs the unramifiedness; the theorem below does not, and at a ramified `𝔭` it
compares overlapping fibers rather than blocks of a partition.
The bijection is not conjugation itself but the pointwise action `𝔓 ↦ c • 𝔓` of a witnessing
element `c`; Mathlib's `IsArithFrobAt.conj` is what transports the Frobenius condition along
it, sending a Frobenius `σ` at `𝔓` to the Frobenius `c * σ * c⁻¹` at `c • 𝔓`.

## Main results

* `NumberField.Chebotarev.frobeniusFiber_card_eq_of_isConj` — conjugate Frobenius elements
  have equipotent fibers above a fixed prime of the base.

## Implementation notes

The source states this with an unramifiedness hypothesis on `𝔭`, but never uses it: the
conjugation bijection is available at every prime. It is dropped here, which strengthens
the statement and keeps the argument list free of an unused binder.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (p. 143).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix.
* Birkbeck–Brasca, [chebotarev-density](https://github.com/CBirkbeck/chebotarev-density)
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/FixedFieldDensity.lean`, declaration `frobeniusFibre_card_eq_of_isConj`
  (source line 54). The statement and proof below are adapted from that declaration.
-/

public section

open scoped NumberField Pointwise

namespace NumberField.Chebotarev

private theorem exists_isArithFrobAt_smul {K L : Type*} [Field K] [Field L]
    [Algebra K L] {𝔭 : Ideal (𝓞 K)} {σ τ c : L ≃ₐ[K] L}
    {𝔓 : Ideal (𝓞 L)} (hτ : c * σ * c⁻¹ = τ)
    (h : ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓) :
    ∃ (_ : (c • 𝔓).IsPrime) (_ : (c • 𝔓).LiesOver 𝔭) (_ : c • 𝔓 ≠ ⊥),
      IsArithFrobAt (𝓞 K) τ (c • 𝔓) := by
  obtain ⟨_, _, hne, hfrob⟩ := h
  refine ⟨inferInstance, inferInstance, ?_, hτ ▸ hfrob.conj c⟩
  simpa using (MulAction.injective c).ne hne

/-- **Equipotent Frobenius fibers.** For `IsConj σ σ'`, the nonzero primes above `𝔭` with
arithmetic Frobenius `σ` are equal in number to those with arithmetic Frobenius `σ'`. -/
theorem frobeniusFiber_card_eq_of_isConj (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (𝔭 : Ideal (𝓞 K)) (σ σ' : L ≃ₐ[K] L)
    (hc : IsConj σ σ') :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ 𝔓} =
      Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ' 𝔓} := by
  -- conjugating by a witnessing element `c` is the bijection between the two fibers
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm c) fun 𝔓 ↦ ?_)
  simp only [MulAction.toPerm_apply]
  refine ⟨exists_isArithFrobAt_smul rfl, fun h ↦ ?_⟩
  -- the reverse direction is the same transport along `c⁻¹`
  simpa using exists_isArithFrobAt_smul (c := c⁻¹) (τ := σ) (by group) h

end NumberField.Chebotarev
