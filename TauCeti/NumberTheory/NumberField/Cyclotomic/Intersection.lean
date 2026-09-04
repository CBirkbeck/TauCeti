/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.IrreducibleOfUnramified

/-!
# A cyclotomic extension meets an unramified extension trivially

Let `A` and `B` be intermediate fields of `Ω / K`, with `B` a `q`-th cyclotomic extension of `K`
for a prime `q`, and suppose every prime of `𝓞 A` above `q` is unramified over `ℤ`. Then
`A ⊓ B = ⊥`.

The reason is a ramification count. `B / K` is totally ramified above `q` — the ramification index
of any prime `𝔔` of `𝓞 B` above `q` is `φ q`, which is also `[B : K]`. Unramifiedness of `A` above
`q` passes down to `E := A ⊓ B`, so `E / K` contributes nothing to that ramification, and
multiplicativity in the tower `𝓞 K ⊆ 𝓞 E ⊆ 𝓞 B` hands the whole of `φ q` to `B / E`. Since the
ramification index is bounded by the degree, `φ q ≤ [B : E]`, while `[E : K] * [B : E] = φ q`.
Hence `[E : K] = 1`.

## Main results

* `IsCyclotomicExtension.inf_eq_bot_of_unramified`: `A ⊓ B = ⊥`.

## References

This is Layer 7.3 of the Chebotarev roadmap (`TauCetiRoadmap/Chebotarev`, `README.md`), which
states the argument used here: by Layer 7.2 the cyclotomic extension is totally ramified above
`q`, `A` is unramified there, and an extension that is both is trivial.

Milne, *Algebraic Number Theory*, proof of Proposition 6.2; Sharifi, *Algebraic Number Theory*,
proof of Lemma 3.1.13. Both run this argument with `K = ℚ`.
-/

public section

open scoped NumberField
open Polynomial TauCeti.RamificationInertia TauCeti.NumberField

namespace IsCyclotomicExtension

/-- **A cyclotomic extension meets an unramified extension trivially.** If `B` is a `q`-th
cyclotomic extension of `K` for a prime `q`, and every prime of `𝓞 A` above `q` is unramified
over `ℤ`, then `A ⊓ B = ⊥`.

`B / K` is totally ramified above `q` while `A`, and hence `A ⊓ B`, is unramified there, so the
intersection can contribute no ramification and must be trivial. -/
theorem inf_eq_bot_of_unramified {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (q : ℕ) (hq : q.Prime) (A B : IntermediateField K Ω) [NumberField A] [NumberField B]
    [IsCyclotomicExtension {q} K B]
    (hur : ∀ (P : Ideal (𝓞 A)) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})],
      Algebra.IsUnramifiedAt ℤ P) :
    A ⊓ B = ⊥ := by
  set E := (A ⊓ B : IntermediateField K Ω) with hE
  have : Fact q.Prime := ⟨hq⟩
  have hEA : E ≤ A := inf_le_left
  have hEB : E ≤ B := inf_le_right
  have : Module.Finite K E := Module.Finite.of_injective
    (IntermediateField.inclusion hEA).toLinearMap (IntermediateField.inclusion hEA).injective
  have : NumberField E := .of_module_finite K _
  let : Algebra E B := (IntermediateField.inclusion hEB).toAlgebra
  let : IsScalarTower K E B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨𝔔, h𝔔max, h𝔔lo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (Ideal.span {(q : ℤ)}) (S := 𝓞 B)
  have := h𝔔max
  have := h𝔔lo
  have hurK : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(q : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮 := fun 𝔮 ↦ isUnramifiedAt_of_forall_isUnramifiedAt hur 𝔮
  -- `B / K` is totally ramified above `q`, and `[B : K] = φ q`
  have htot : 𝔔.ramificationIdx (𝓞 K) = q.totient := by
    have : IsCyclotomicExtension {q ^ (0 + 1)} K B := by
      simpa using ‹IsCyclotomicExtension {q} K B›
    simpa using IsCyclotomicExtension.ramificationIdx_eq_totient (K := K) q 0 hurK 𝔔
  have hBK : Module.finrank K B = q.totient :=
    IsCyclotomicExtension.finrank B
      (IsCyclotomicExtension.irreducible_cyclotomic_of_unramified K q hq hurK)
  -- `E` is unramified above `q`, so it carries none of that ramification
  have : Algebra.IsUnramifiedAt ℤ (𝔔.under (𝓞 E)) := isUnramifiedAt_of_forall_isUnramifiedAt hur _
  have : Algebra.IsUnramifiedAt (𝓞 K) (𝔔.under (𝓞 E)) := .of_restrictScalars ℤ _
  have he1 : (𝔔.under (𝓞 E)).ramificationIdx (𝓞 K) = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (𝔔.under (𝓞 E)) 𝔔
  have he2 : 𝔔.ramificationIdx (𝓞 E) = q.totient := by
    rw [htot, he1, one_mul] at htower; exact htower.symm
  -- so all `φ q` of it lives in `B / E`, forcing `[E : K] = 1`
  exact IntermediateField.finrank_eq_one_iff.mp
    (finrank_eq_one_of_ramificationIdx_eq_finrank 𝔔 he2 hBK)

end IsCyclotomicExtension
