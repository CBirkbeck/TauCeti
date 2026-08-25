/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.RingTheory.Huber.Basic

/-!
# Extending a valuation from a ring of definition to the whole Huber ring

A ring of definition `A₀` of a Huber ring `A` is open, so a topologically nilpotent `s`
multiplies every element of `A` into it: `TauCeti.Huber.PairOfDefinition.exists_pow_mul_mem`
gives an `n` with `sⁿ * a ∈ A₀`. A valuation `w` of `A₀` that does not vanish at `s` therefore
has only one possible extension to `A`,

`v a = w (sⁿ * a) * (w s)⁻ⁿ`,

and this file shows that formula is well defined and is a valuation.

## Why this is not `Valuation.extendToLocalization`

Mathlib extends a valuation along a localisation that inverts a set on which the valuation is
nonzero. That does not apply here: `s` is *topologically* nilpotent, not a unit, so `A` is in
general not `A₀[1/s]` — there need be no ring map `A₀[1/s] → A` at all. Take `A = ℤ_[p]` with
`A₀ = A` and `s = p`. What is true, and is all the formula needs, is the one-sided statement
that every element of `A` is carried into `A₀` by a power of `s`.

## Well-definedness

Independence of `n` reduces to the case of comparing `n` with `n + j`, where
`s ^ (n + j) * a = s ^ j * (sⁿ * a)` splits off a factor whose `w`-value is `(w s) ^ j`, exactly
cancelling the extra `(w s)⁻ʲ`. Two arbitrary exponents are then compared through their sum.

The valuation axioms follow the same pattern: a common exponent is chosen for the two arguments
— their sum for a product, since `s ^ (m + n) * (x * y) = (sᵐ * x) * (sⁿ * y)`, and again their
sum for a sum, where both terms need the *same* exponent — and the axiom is then inherited from
`w` after the shared factor `(w s)⁻ⁿ` is divided out.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.extendValuation` : the extension.

## Main results

* `TauCeti.Huber.PairOfDefinition.extendValuation_apply` : its defining formula, at **every**
  exponent that works, not just the chosen one. This is the interface; the definition goes
  through `Classical.choose` and is not meant to be unfolded.
* `TauCeti.Huber.PairOfDefinition.extendValuation_coe` : it restricts to `w` on `A₀`.
* `TauCeti.Huber.PairOfDefinition.pow_mul_mem_of_le` : raising the exponent keeps the product
  in the ring of definition.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.44(3), which is where
  this extension is used.

## Provenance

Adapted from [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch
`dev/adic-spaces`, commit `37bbdaeb9`, `projects/AdicSpaces/Adic spaces/Lemma745.lean`,
declarations `vExtFun_step`, `vExtFun_well_defined`, `vExtFun_map_mul`,
`vExtFun_map_add_le_max` and `exists_valuation_extension`. **Adapted, not copied**: that
development states the result existentially, as `∃ v_ext, …`, and threads the value `w s`
through five separate lemmas as an explicit parameter with its own defining equation. Here the
extension is a `def`, so it can be named and rewritten at a call site, the arithmetic is one
private lemma rather than four public ones, and the exponent-raising step is public because it
is reusable on its own.
-/

public section

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Raising the exponent keeps the product in the ring of definition**: `s ^ (k + j) * a`
splits as `s ^ j * (s ^ k * a)`, and both factors lie in `A₀`. -/
theorem pow_mul_mem_of_le (P : PairOfDefinition A) {s : A} (hs : s ∈ P.ringOfDefinition)
    {a : A} {k : ℕ} (hk : s ^ k * a ∈ P.ringOfDefinition) (j : ℕ) :
    s ^ (k + j) * a ∈ P.ringOfDefinition := by
  rw [show s ^ (k + j) * a = s ^ j * (s ^ k * a) by rw [add_comm, pow_add, mul_assoc]]
  exact P.ringOfDefinition.mul_mem (P.ringOfDefinition.pow_mem hs j) hk

/-- The quotient `w (sⁿ * a) * (w s)⁻ⁿ` does not depend on `n`. Both exponents are compared
with their sum, where the extra factor of `s` contributes `(w s) ^ j` and cancels. -/
private theorem extend_aux (P : PairOfDefinition A) (w : Valuation P.ringOfDefinition Γ₀)
    {s : A} (hs : s ∈ P.ringOfDefinition) (hw : w ⟨s, hs⟩ ≠ 0) {a : A} {m n : ℕ}
    (hm : s ^ m * a ∈ P.ringOfDefinition) (hn : s ^ n * a ∈ P.ringOfDefinition) :
    w ⟨s ^ m * a, hm⟩ * (w ⟨s, hs⟩)⁻¹ ^ m = w ⟨s ^ n * a, hn⟩ * (w ⟨s, hs⟩)⁻¹ ^ n := by
  have hcancel : w ⟨s, hs⟩ ^ n * (w ⟨s, hs⟩)⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
  -- one step: comparing `k` with `k + j`
  have step : ∀ {k : ℕ} (hk : s ^ k * a ∈ P.ringOfDefinition) (j : ℕ),
      w ⟨s ^ k * a, hk⟩ * (w ⟨s, hs⟩)⁻¹ ^ k =
        w ⟨s ^ (k + j) * a, P.pow_mul_mem_of_le hs hk j⟩ * (w ⟨s, hs⟩)⁻¹ ^ (k + j) := by
    intro k hk j
    have hsplit : (⟨s ^ (k + j) * a, P.pow_mul_mem_of_le hs hk j⟩ : P.ringOfDefinition) =
        ⟨s, hs⟩ ^ j * ⟨s ^ k * a, hk⟩ :=
      Subtype.ext (by push_cast; ring)
    have hj : w ⟨s, hs⟩ ^ j * (w ⟨s, hs⟩)⁻¹ ^ j = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
    rw [hsplit, map_mul, map_pow, pow_add, mul_comm (w ⟨s, hs⟩ ^ j), mul_mul_mul_comm, hj,
      mul_one]
  -- compare both exponents with their sum
  rw [step hm n, step hn m]
  exact congrArg₂ (· * ·) (congrArg w (Subtype.ext (by push_cast; ring)))
    (by rw [Nat.add_comm])

/-- The underlying function of `extendValuation`, `a ↦ w (sⁿ * a) * (w s)⁻ⁿ` at a chosen `n`.
Use `extendValuation_apply`, which is valid at every workable `n`, rather than unfolding. -/
private noncomputable def extendFun [IsTopologicalRing A] (P : PairOfDefinition A)
    (w : Valuation P.ringOfDefinition Γ₀) {s : A} (hs : s ∈ P.ringOfDefinition)
    (hnil : IsTopologicallyNilpotent s) (a : A) : Γ₀ :=
  w ⟨s ^ (P.exists_pow_mul_mem hnil a).choose * a, (P.exists_pow_mul_mem hnil a).choose_spec⟩
    * (w ⟨s, hs⟩)⁻¹ ^ (P.exists_pow_mul_mem hnil a).choose

private theorem extendFun_apply [IsTopologicalRing A] (P : PairOfDefinition A)
    (w : Valuation P.ringOfDefinition Γ₀) {s : A} (hs : s ∈ P.ringOfDefinition)
    (hnil : IsTopologicallyNilpotent s) (hw : w ⟨s, hs⟩ ≠ 0) (a : A) {n : ℕ}
    (hn : s ^ n * a ∈ P.ringOfDefinition) :
    extendFun P w hs hnil a = w ⟨s ^ n * a, hn⟩ * (w ⟨s, hs⟩)⁻¹ ^ n :=
  P.extend_aux w hs hw _ hn

private theorem extendFun_coe [IsTopologicalRing A] (P : PairOfDefinition A)
    (w : Valuation P.ringOfDefinition Γ₀) {s : A} (hs : s ∈ P.ringOfDefinition)
    (hnil : IsTopologicallyNilpotent s) (hw : w ⟨s, hs⟩ ≠ 0) (a : P.ringOfDefinition) :
    extendFun P w hs hnil (a : A) = w a := by
  rw [extendFun_apply P w hs hnil hw (a : A) (n := 0) (by simp)]
  simp

/-- **The extension of `w` from the ring of definition to `A`.** For any `n` with
`sⁿ * a ∈ A₀` — one exists because `A₀` is open and `s` is topologically nilpotent — the value
is `w (sⁿ * a) * (w s)⁻ⁿ`, and `extendValuation_apply` says so at every such `n`. -/
noncomputable def extendValuation [IsTopologicalRing A] (P : PairOfDefinition A)
    (w : Valuation P.ringOfDefinition Γ₀) {s : A} (hs : s ∈ P.ringOfDefinition)
    (hnil : IsTopologicallyNilpotent s) (hw : w ⟨s, hs⟩ ≠ 0) : Valuation A Γ₀ where
  toFun := extendFun P w hs hnil
  map_zero' := by
    rw [show (0 : A) = ((0 : P.ringOfDefinition) : A) from rfl, extendFun_coe P w hs hnil hw]
    exact map_zero _
  map_one' := by
    rw [show (1 : A) = ((1 : P.ringOfDefinition) : A) from rfl, extendFun_coe P w hs hnil hw]
    exact map_one _
  map_mul' x y := by
    obtain ⟨m, hm⟩ := P.exists_pow_mul_mem hnil x
    obtain ⟨n, hn⟩ := P.exists_pow_mul_mem hnil y
    have hxy : s ^ (m + n) * (x * y) ∈ P.ringOfDefinition := by
      rw [show s ^ (m + n) * (x * y) = (s ^ m * x) * (s ^ n * y) by ring]
      exact P.ringOfDefinition.mul_mem hm hn
    rw [extendFun_apply P w hs hnil hw _ hxy, extendFun_apply P w hs hnil hw _ hm,
      extendFun_apply P w hs hnil hw _ hn,
      show (⟨s ^ (m + n) * (x * y), hxy⟩ : P.ringOfDefinition) =
        ⟨s ^ m * x, hm⟩ * ⟨s ^ n * y, hn⟩ from Subtype.ext (by push_cast; ring),
      map_mul, pow_add]
    exact mul_mul_mul_comm _ _ _ _
  map_add_le_max' x y := by
    -- a sum needs one exponent that works for both terms, so take the sum of the two
    obtain ⟨m, hm⟩ := P.exists_pow_mul_mem hnil x
    obtain ⟨n, hn⟩ := P.exists_pow_mul_mem hnil y
    have hx : s ^ (m + n) * x ∈ P.ringOfDefinition := P.pow_mul_mem_of_le hs hm n
    have hy : s ^ (m + n) * y ∈ P.ringOfDefinition := by
      rw [Nat.add_comm]; exact P.pow_mul_mem_of_le hs hn m
    have hxy : s ^ (m + n) * (x + y) ∈ P.ringOfDefinition := by
      rw [mul_add]; exact P.ringOfDefinition.add_mem hx hy
    rw [extendFun_apply P w hs hnil hw _ hxy, extendFun_apply P w hs hnil hw _ hx,
      extendFun_apply P w hs hnil hw _ hy,
      show (⟨s ^ (m + n) * (x + y), hxy⟩ : P.ringOfDefinition) =
        ⟨s ^ (m + n) * x, hx⟩ + ⟨s ^ (m + n) * y, hy⟩ from Subtype.ext (by push_cast; ring)]
    rcases le_max_iff.mp (w.map_add ⟨s ^ (m + n) * x, hx⟩ ⟨s ^ (m + n) * y, hy⟩) with h | h
    · exact le_max_of_le_left (mul_le_mul' h le_rfl)
    · exact le_max_of_le_right (mul_le_mul' h le_rfl)

/-- **The defining formula**, at every exponent that carries `a` into the ring of definition. -/
theorem extendValuation_apply [IsTopologicalRing A] (P : PairOfDefinition A)
    (w : Valuation P.ringOfDefinition Γ₀) {s : A} (hs : s ∈ P.ringOfDefinition)
    (hnil : IsTopologicallyNilpotent s) (hw : w ⟨s, hs⟩ ≠ 0) (a : A) {n : ℕ}
    (hn : s ^ n * a ∈ P.ringOfDefinition) :
    P.extendValuation w hs hnil hw a = w ⟨s ^ n * a, hn⟩ * (w ⟨s, hs⟩)⁻¹ ^ n :=
  extendFun_apply P w hs hnil hw a hn

/-- **The extension restricts to `w`** on the ring of definition. -/
@[simp]
theorem extendValuation_coe [IsTopologicalRing A] (P : PairOfDefinition A)
    (w : Valuation P.ringOfDefinition Γ₀) {s : A} (hs : s ∈ P.ringOfDefinition)
    (hnil : IsTopologicallyNilpotent s) (hw : w ⟨s, hs⟩ ≠ 0) (a : P.ringOfDefinition) :
    P.extendValuation w hs hnil hw (a : A) = w a :=
  extendFun_coe P w hs hnil hw a

end TauCeti.Huber.PairOfDefinition
