/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.NumberTheory.RamificationInertia.Tower

/-!
# Ramification indices in an extension of number fields

Two consequences of the general ramification bounds for the rings of integers of number fields.
`TauCeti.NumberTheory.RamificationInertia.Tower` states them for a finite flat extension of
domains; here they are transported to the fields themselves, where the degree in question is
`[F : K]` rather than the rank of `𝓞 F` over `𝓞 K`, and specialised to the absolute case over `ℤ`.

## Main results

* `TauCeti.NumberField.ramificationIdx_le_finrank`: for a prime `𝔔` of `𝓞 F` in an extension
  `F / K` of number fields, `e(𝔔 / 𝓞 K) ≤ [F : K]`.
* `TauCeti.NumberField.ramificationIdx_under_eq_one`: if a rational prime `p` is unramified in
  `K`, then the prime of `𝓞 K` below any prime of `𝓞 F` above `p` has `e = 1` over `ℤ`.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A relative ramification index is at most the degree of the extension.** For a prime `𝔔` of
`𝓞 F` in an extension `F / K` of number fields, `e(𝔔 / 𝓞 K) ≤ [F : K]`.

This is `TauCeti.RamificationInertia.ramificationIdx_le_finrank` for the rings of integers,
transported along `IsFractionRing.finrank_eq` so that the bound is the degree of the field
extension rather than the rank of `𝓞 F` over `𝓞 K`. -/
theorem ramificationIdx_le_finrank {F : Type*} [Field F] [NumberField F] [Algebra K F]
    (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] : 𝔔.ramificationIdx (𝓞 K) ≤ Module.finrank K F :=
  -- The fundamental identity `∑ eᵢ fᵢ = [F : K]` bounds each `eᵢ`, and `[𝓞 F : 𝓞 K] = [F : K]`.
  (TauCeti.RamificationInertia.ramificationIdx_le_finrank (𝔔.under (𝓞 K)) 𝔔).trans_eq
    (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 F) F).symm

/-- **Unramifiedness in the base makes the prime below have absolute index one.** If every prime
of `𝓞 K` above the rational prime `p` is unramified over `ℤ`, then for any prime `𝔔` of `𝓞 F`
above `p` the prime `𝔔 ∩ 𝓞 K` has `e(𝔔 ∩ 𝓞 K / p) = 1`.

`hur` is definitionally Mathlib's `Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})`, so a
proof of that predicate can be passed directly. -/
theorem ramificationIdx_under_eq_one (p : ℕ) {F : Type*} [Field F] [Algebra K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
    Algebra.IsUnramifiedAt ℤ 𝔮) (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime]
    [𝔔.LiesOver (Ideal.span {(p : ℤ)})] : (𝔔.under (𝓞 K)).ramificationIdx ℤ = 1 :=
  -- `𝔮 = 𝔔 ∩ 𝓞 K` lies above `p`, which is unramified in `K`, so `e(𝔮 / p) = 1`.
  Ideal.ramificationIdx_eq_one_iff.mpr (hur _)

end TauCeti.NumberField
