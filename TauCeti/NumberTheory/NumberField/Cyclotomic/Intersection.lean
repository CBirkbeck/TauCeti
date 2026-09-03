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

Milne, *Algebraic Number Theory*, proof of Proposition 6.2; Sharifi, *Algebraic Number Theory*,
proof of Lemma 3.1.13. Both run this argument with `K = ℚ`.
-/

public section

open scoped NumberField
open Polynomial

namespace IsCyclotomicExtension

/-- Unramifiedness above a rational prime descends along an integral extension: if every prime of
`A` above `q` is unramified over `ℤ`, then so is every prime of a subring `S` below it.

Stated at the level of rings rather than of fields because it is used twice at different bases —
once for `𝓞 K` and once for `𝓞 (A ⊓ B)`. -/
theorem isUnramifiedAt_of_isIntegral {S A : Type*} [CommRing S] [CommRing A] [IsDomain A]
    [IsDedekindDomain S] [Algebra S A] [Module.Finite S A] [FaithfulSMul S A]
    [Module.IsTorsionFree S A] [Algebra.EssFiniteType ℤ S] [Algebra.EssFiniteType ℤ A] {q : ℕ}
    (hur : ∀ (P : Ideal A) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})],
      Algebra.IsUnramifiedAt ℤ P)
    (𝔮 : Ideal S) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(q : ℤ)})] :
    Algebra.IsUnramifiedAt ℤ 𝔮 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (𝔮.primesOver A))
  have : (P : Ideal A).IsPrime := P.2.1
  have : (P : Ideal A).LiesOver 𝔮 := P.2.2
  have : (P : Ideal A).LiesOver (Ideal.span {(q : ℤ)}) :=
    Ideal.LiesOver.trans (P : Ideal A) 𝔮 (Ideal.span {(q : ℤ)})
  exact Algebra.IsUnramifiedAt.of_liesOver ℤ 𝔮 (P : Ideal A)

/-- **A totally ramified prime leaves no room for an intermediate field.** In a tower
`K ≤ E ≤ B` of number fields, if a prime of `𝓞 B` is already as ramified over `𝓞 E` as the whole
degree `[B : K]` allows, then `[E : K] = 1`.

The ramification index over `𝓞 E` is bounded by `[B : E]`, so `[B : K] ≤ [B : E]`; against
`[E : K] * [B : E] = [B : K]` that forces `[E : K] = 1`. -/
private theorem finrank_eq_one_of_ramificationIdx_eq_finrank {K Ω : Type*} [Field K] [Field Ω]
    [Algebra K Ω] (E B : IntermediateField K Ω) [NumberField E] [NumberField B] [Algebra E B]
    [IsScalarTower K E B] [Module.Finite K E] (𝔔 : Ideal (𝓞 B)) [𝔔.IsPrime] {n : ℕ}
    (he : 𝔔.ramificationIdx (𝓞 E) = n) (hB : Module.finrank K B = n) :
    Module.finrank K E = 1 := by
  have hb := Ideal.ramificationIdx_le_finrank_numberField (K := E) (F := B) 𝔔
  have hle : Module.finrank K E * Module.finrank E B ≤ 1 * Module.finrank E B := by
    rw [one_mul, Module.finrank_mul_finrank K E B, hB, ← he]; exact hb
  exact le_antisymm (Nat.le_of_mul_le_mul_right hle Module.finrank_pos) Module.finrank_pos

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
      Algebra.IsUnramifiedAt ℤ 𝔮 := fun 𝔮 ↦ isUnramifiedAt_of_isIntegral hur 𝔮
  -- `B / K` is totally ramified above `q`, and `[B : K] = φ q`
  have htot : 𝔔.ramificationIdx (𝓞 K) = q.totient := by
    have : IsCyclotomicExtension {q ^ (0 + 1)} K B := by
      simpa using ‹IsCyclotomicExtension {q} K B›
    simpa using IsCyclotomicExtension.ramificationIdx_eq_totient (K := K) q 0 hurK 𝔔
  have hBK : Module.finrank K B = q.totient :=
    IsCyclotomicExtension.finrank B
      (IsCyclotomicExtension.irreducible_cyclotomic_of_unramified K q hq hurK)
  -- `E` is unramified above `q`, so it carries none of that ramification
  have : Algebra.IsUnramifiedAt ℤ (𝔔.under (𝓞 E)) := isUnramifiedAt_of_isIntegral hur _
  have : Algebra.IsUnramifiedAt (𝓞 K) (𝔔.under (𝓞 E)) := .of_restrictScalars ℤ _
  have he1 : (𝔔.under (𝓞 E)).ramificationIdx (𝓞 K) = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (𝔔.under (𝓞 E)) 𝔔
  have he2 : 𝔔.ramificationIdx (𝓞 E) = q.totient := by
    rw [htot, he1, one_mul] at htower; exact htower.symm
  -- so all `φ q` of it lives in `B / E`, forcing `[E : K] = 1`
  exact IntermediateField.finrank_eq_one_iff.mp
    (finrank_eq_one_of_ramificationIdx_eq_finrank E B 𝔔 he2 hBK)

end IsCyclotomicExtension
