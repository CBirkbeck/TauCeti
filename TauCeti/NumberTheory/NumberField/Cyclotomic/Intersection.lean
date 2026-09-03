/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.IrreducibleOfUnramified

/-!
# A cyclotomic extension meets an unramified extension trivially

Let `K` be a number field, `q` a prime, and `A`, `B` intermediate fields of an extension `Ω / K`
with `B` a `q`-th cyclotomic extension of `K`. If `q` is unramified in `A`, then `A ⊓ B = ⊥`.

The mechanism is ramification on both sides at once. `B / K` is *totally ramified* above `q`:
every prime of `𝓞 B` over `q` has ramification index `φ(q) = [B : K]`, which is
`IsCyclotomicExtension.ramificationIdx_eq_totient`. Ramification indices multiply in towers, so
for the intermediate field `E = A ⊓ B` the index `e(𝔓_E / q)` is forced up to `[E : K]`. But `E`
sits inside `A`, where `q` is unramified, so `e(𝔓_E / q) = 1`. Hence `[E : K] = 1` and `E = ⊥`.

An extension that is simultaneously totally ramified and unramified at a prime is trivial: that
is the whole content, and the two halves come from the two sides of the intersection.
-/

public section

open scoped NumberField
open Polynomial

namespace IsCyclotomicExtension

/-- **A cyclotomic extension meets an unramified extension trivially.** If `q` is unramified in
`A` and `B` is a `q`-th cyclotomic extension of `K`, then `A ⊓ B = ⊥` inside `Ω`.

`hur` is stated on `A` rather than on `K`: unramifiedness in `A` is strictly stronger, and is the
only place this hypothesis is used beyond what `ramificationIdx_eq_totient` already needs. -/
theorem inf_eq_bot_of_unramified {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (q : ℕ) (hq : q.Prime) (A B : IntermediateField K Ω) [NumberField A]
    [IsCyclotomicExtension {q} K B]
    (hur : ∀ (𝔓 : Ideal (𝓞 A)) [𝔓.IsPrime] [𝔓.LiesOver (Ideal.span {(q : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔓) :
    A ⊓ B = ⊥ := by
  -- `E = A ⊓ B` is a number field: it sits inside `A`, which is one, and finiteness descends
  -- along the inclusion.  (Verified; `NumberField ↥(A ⊓ B)` is not found by instance search.)
  have hle : (A ⊓ B : IntermediateField K Ω) ≤ A := inf_le_left
  have : Module.Finite K (A ⊓ B : IntermediateField K Ω) := Module.Finite.of_injective
    (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective
  have : NumberField (A ⊓ B : IntermediateField K Ω) := .of_module_finite K _
  -- Remaining: the two-sided ramification argument.
  --   e(𝔔/𝓞 K) = φ(q) = [B : K]                       (ramificationIdx_eq_totient, q = q^(0+1))
  --   e(𝔔/𝓞 K) = e(𝔓/𝓞 K) * e(𝔔/𝓞 E)                  (Ideal.ramificationIdx_tower)
  --   e(𝔓/𝓞 K) ≤ [E : K],  e(𝔔/𝓞 E) ≤ [B : E]         (ramificationIdx_le_finrank)
  --   [B : K] = [E : K] * [B : E]                     (finrank tower)
  -- forcing e(𝔓/𝓞 K) = [E : K]; unramifiedness of `q` in `A` descends to `E`, giving
  -- e(𝔓/𝓞 K) = 1, hence finrank K E = 1 and `E = ⊥` by `IntermediateField.finrank_eq_one_iff`.
  sorry

end IsCyclotomicExtension
