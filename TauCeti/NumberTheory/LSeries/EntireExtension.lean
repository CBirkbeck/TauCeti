/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.Convergence

/-!
# Analytic continuation predicates for L-series

The two analytic-continuation obligations of Hecke theory, as predicates on a coefficient
sequence `a : ℕ → ℂ`:

* `LSeries.HasEntireExtension a`: the abscissa of absolute convergence is finite and some
  entire function agrees with `LSeries a` on the (nonempty) convergence half-plane. Such
  an extension is unique (`LSeries.HasEntireExtension.unique`) by analytic continuation.
* `LSeries.HasMeromorphicExtensionWithPole a`: the abscissa is finite and a globally
  meromorphic witness agrees with `LSeries a` on the convergence half-plane while having
  a genuine pole (negative meromorphic order) somewhere — the obligation shape ruling out
  entirety, e.g. for Eisenstein L-functions.

Supporting general lemmas:

* `meromorphicOrderAt_div_neg_of_orderAt_lt`: a quotient of meromorphic functions with
  finite orders has a pole where the numerator's order is smaller.
* `LSeries.coprimeStrip`: the coefficient sequence stripped at a finite set of primes,
  zeroed on multiples — the elementary Euler-factor-removal operation.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/LFunction.lean`), as Layer-7 groundwork for the
functional-equation and converse-theorem milestones.

## References

* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>
  (`Modularforms/LFunction.lean`)
-/

public section

namespace LSeries

open Filter

/-- **Hecke entire-continuation predicate.** A coefficient sequence `a : ℕ → ℂ` *has an
entire extension* if its abscissa of absolute convergence is finite — so the agreement
region below is a genuine half-plane, not vacuously empty — and some entire `F : ℂ → ℂ`
agrees with `LSeries a` on it. The extension is unique (`HasEntireExtension.unique`). -/
def HasEntireExtension (a : ℕ → ℂ) : Prop :=
  abscissaOfAbsConv a < ⊤ ∧
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s

namespace HasEntireExtension

variable {a : ℕ → ℂ}

/-- **Uniqueness of the entire extension**: two entire functions that both extend
`LSeries a` on the absolute-convergence half-plane are equal everywhere on `ℂ`. -/
theorem unique {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h_finite : abscissaOfAbsConv a < ⊤)
    (hFa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s)
    (hGa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → G s = LSeries a s) :
    F = G := by
  obtain ⟨σ, hσ_abs, -⟩ := EReal.exists_between_coe_real h_finite
  set U : Set ℂ := {s : ℂ | (σ : ℝ) < s.re} with hU_def
  have hU_sub : ∀ s ∈ U, abscissaOfAbsConv a < (s.re : EReal) := fun s hs ↦
    lt_of_lt_of_le hσ_abs (by exact_mod_cast (hs : (σ : ℝ) < s.re).le)
  have hz₀ : ((σ + 1 : ℝ) : ℂ) ∈ U := by
    have h_re : ((σ + 1 : ℝ) : ℂ).re = σ + 1 := Complex.ofReal_re _
    simp only [hU_def, Set.mem_ofPred_eq, h_re]
    linarith
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG)
    (Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨U, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀,
        fun s hs ↦ (hFa (hU_sub s hs)).trans (hGa (hU_sub s hs)).symm⟩)

end HasEntireExtension

/-- **A quotient of meromorphic functions has a pole where the numerator's order is
smaller**: if `num` and `den` are meromorphic at `x` with finite orders and
`order num < order den`, then `num / den` has negative meromorphic order at `x`. -/
theorem _root_.meromorphicOrderAt_div_neg_of_orderAt_lt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {num den : 𝕜 → 𝕜} {x : 𝕜}
    (h_num : MeromorphicAt num x) (h_den : MeromorphicAt den x)
    (h_num_finite : meromorphicOrderAt num x ≠ ⊤)
    (h_den_finite : meromorphicOrderAt den x ≠ ⊤)
    (h_lt : meromorphicOrderAt num x < meromorphicOrderAt den x) :
    meromorphicOrderAt (num / den) x < 0 := by
  rw [div_eq_mul_inv, meromorphicOrderAt_mul h_num h_den.inv, meromorphicOrderAt_inv]
  lift meromorphicOrderAt num x to ℤ using h_num_finite with n hn
  lift meromorphicOrderAt den x to ℤ using h_den_finite with m hm
  rw [WithTop.coe_lt_coe] at h_lt
  have h_neg : -((m : ℤ) : WithTop ℤ) = (((-m) : ℤ) : WithTop ℤ) := rfl
  have h_zero : (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := rfl
  rw [h_neg, ← WithTop.coe_add, h_zero, WithTop.coe_lt_coe]
  lia

/-- **Meromorphic extension with a pole.** A coefficient sequence `a : ℕ → ℂ` (with
finite abscissa of absolute convergence, so the agreement clause is not vacuous) *has a
meromorphic extension with a pole* if some `g : ℂ → ℂ`, meromorphic at every point of
`ℂ`, agrees with `LSeries a` on the absolute-convergence half-plane and has a genuine
pole (negative meromorphic order) at some `s₀`. This is the obligation shape ruling out
an entire extension: an entire extension would agree with `g` on the half-plane, hence —
by analytic continuation off the polar set — near `s₀`, where `g` blows up. -/
def HasMeromorphicExtensionWithPole (a : ℕ → ℂ) : Prop :=
  abscissaOfAbsConv a < ⊤ ∧
    ∃ (g : ℂ → ℂ) (s₀ : ℂ),
      (∀ z : ℂ, MeromorphicAt g z) ∧
      meromorphicOrderAt g s₀ < 0 ∧
      ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → g s = LSeries a s

/-- **The coprime-stripped coefficient sequence**: `f` zeroed at every `n` divisible by a
prime of the finite set `S`, unchanged elsewhere — the elementary operation of removing
the Euler factors at `S`. -/
def coprimeStrip (S : Finset Nat.Primes) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ if ∀ p ∈ S, ¬ (p : ℕ) ∣ n then f n else 0

/-- `coprimeStrip S f 1 = f 1`: no prime divides `1`. -/
@[simp]
lemma coprimeStrip_one (S : Finset Nat.Primes) (f : ℕ → ℂ) :
    coprimeStrip S f 1 = f 1 := by
  unfold coprimeStrip
  rw [if_pos fun p _ h_dvd ↦ p.prop.one_lt.ne' (Nat.dvd_one.mp h_dvd)]

end LSeries
