/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.On

/-!
# Concatenating set-level Cauchy principal values

`HasCauchyPV` binds its finite excision set **existentially**, which is the right interface for
consumers but is too weak to concatenate: two principal values along adjacent subcurves may be
witnessed by *different* excision sets, and passing to their union changes the excised integrand.
Recovering the union form needs the extra points to be met on a null set of parameters — a genuine
side condition, since a curve that is *constant* at an added point meets it on a set of positive
measure.

This file therefore exposes the prescribed-witness form `HasCauchyPVWith`, in which the excision
set is an explicit parameter, and concatenates there. Adjacent subcurves sharing one excision set
add (`HasCauchyPVWith.concat`), and the complementary piece can be subtracted off
(`HasCauchyPVWith.sub_right`) — the direction that splits a principal value along a closed contour
into its constituent arcs. Both are the set-level analogues of `HasCauchyPVAt.concat`, whose single
excised point is automatically shared.

## Main definitions

* `TauCeti.Contour.HasCauchyPVWith` — `HasCauchyPV` with the excision set prescribed rather than
  existentially bound.

## Main results

* `TauCeti.Contour.hasCauchyPV_iff_exists_hasCauchyPVWith` — the two forms agree after
  existentially quantifying the witness.
* `TauCeti.Contour.HasCauchyPVWith.concat` — principal values along `[a, b]` and `[b, c]` sharing
  an excision set add to the one along `[a, c]`.
* `TauCeti.Contour.HasCauchyPVWith.sub_right` — the converse split: removing the `[b, c]` piece
  from the `[a, c]` principal value leaves the `[a, b]` one.
-/

public section

open Filter Topology MeasureTheory

namespace TauCeti.Contour

/-- **The Cauchy principal value with a prescribed excision set.** Identical to `HasCauchyPV`
except that the finite set `S` of excised points is an explicit parameter rather than
existentially bound, which is what makes the principal values along adjacent subcurves
concatenable. -/
def HasCauchyPVWith (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (S : Finset ℂ) (v : ℂ) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t) volume a b) ∧
    Tendsto (fun ε ↦ ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
      (𝓝[>] 0) (𝓝 v)

/-- `HasCauchyPVWith` unfolded into its two clauses — eventual integrability of the excised
integrand and convergence of the excised integrals — so consumers need not unfold the
definition. -/
theorem hasCauchyPVWith_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} {v : ℂ} :
    HasCauchyPVWith γ a b f S v ↔
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
          (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t) volume a b) ∧
        Tendsto (fun ε ↦ ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
          (𝓝[>] 0) (𝓝 v) :=
  Iff.rfl

/-- Forgetting the witness recovers the existentially-bound form. -/
theorem HasCauchyPVWith.hasCauchyPV {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} {v : ℂ}
    (h : HasCauchyPVWith γ a b f S v) : HasCauchyPV γ a b f v :=
  HasCauchyPV.intro S h.1 h.2

/-- `HasCauchyPV` is exactly `HasCauchyPVWith` with the excision set existentially quantified. -/
theorem hasCauchyPV_iff_exists_hasCauchyPVWith {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ} :
    HasCauchyPV γ a b f v ↔ ∃ S : Finset ℂ, HasCauchyPVWith γ a b f S v := by
  rw [hasCauchyPV_iff]
  exact Iff.rfl

/-- **Concatenation.** Principal values along the adjacent subcurves `[a, b]` and `[b, c]` that
excise the *same* finite set add to the principal value along `[a, c]`. As for
`HasCauchyPVAt.concat`, the integrability of the excised integrand across `[a, c]` and the
additivity of the integral both follow from the two given principal values, so no ordering or
separate integrability hypothesis is needed. -/
theorem HasCauchyPVWith.concat {γ : ℝ → ℂ} {a b c : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} {L₁ L₂ : ℂ}
    (h_ab : HasCauchyPVWith γ a b f S L₁) (h_bc : HasCauchyPVWith γ b c f S L₂) :
    HasCauchyPVWith γ a c f S (L₁ + L₂) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h_ab.1, h_bc.1] with ε hab hbc
    exact hab.trans hbc
  · refine Filter.Tendsto.congr' ?_ (h_ab.2.add h_bc.2)
    filter_upwards [h_ab.1, h_bc.1] with ε hab hbc
    exact intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- **Splitting off the far piece.** If the principal value along `[a, c]` and the one along
`[b, c]` excise the same finite set, then their difference is the principal value along `[a, b]`.
This is the direction that decomposes a contour: knowing the whole and one arc gives the rest. -/
theorem HasCauchyPVWith.sub_right {γ : ℝ → ℂ} {a b c : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} {L L₂ : ℂ}
    (h_ac : HasCauchyPVWith γ a c f S L) (h_bc : HasCauchyPVWith γ b c f S L₂) :
    HasCauchyPVWith γ a b f S (L - L₂) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h_ac.1, h_bc.1] with ε hac hbc
    exact hac.trans hbc.symm
  · refine Filter.Tendsto.congr' ?_ (h_ac.2.sub h_bc.2)
    filter_upwards [h_ac.1, h_bc.1] with ε hac hbc
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := b) (hac.trans hbc.symm) hbc]
    ring

end TauCeti.Contour

end
