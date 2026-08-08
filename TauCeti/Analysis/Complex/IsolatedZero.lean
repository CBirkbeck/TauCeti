/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic

/-!
# Estimates near an isolated zero

A lower bound on a circle around a point at whose centre the function has its only zero, two
ways of concluding that the analytic order at a point is finite, and the finiteness of the zero
set on a compact.

The first two are the standing hypotheses of every Rouché comparison made on such a disc: both
`TauCeti.Analysis.Complex.Conformal.LocalDegree` and
`TauCeti.Analysis.Complex.Conformal.Hurwitz` set up such a comparison, and each needs the same
two facts about the disc before Rouché can be applied. The third has no Rouché content at all: it
draws the same finiteness from the global hypothesis a zero count comes with, that the zeros in an
open set lie in a finite set, and serves the arbitrary-cycle argument principle
(`TauCeti.Contour.argumentPrinciple_nullHomologous_of_analyticOnNhd`). No result here mentions
Rouché's theorem, so this module does not import it:

## Main results

* `TauCeti.exists_pos_le_norm_of_mem_sphere`: on the bounding circle the function is bounded below
  by a positive constant — this is what a competitor has to beat.
* `TauCeti.analyticOrderAt_ne_top_of_forall_ne_zero`: the analytic order at the centre is finite,
  so the count Rouché produces is a natural number rather than `⊤`.
* `TauCeti.analyticOrderAt_ne_top_of_zeros_subset`: the same finiteness under the hypothesis a
  global zero count comes with, that the zeros in an open set lie in a finite set.
* `TauCeti.finite_setOfPred_eq_zero_of_isCompact`: an analytic function somewhere nonzero on a
  preconnected open set has finitely many zeros in any compact subset.

They are separated here only because several files need them.
-/

public section

open Complex Metric Filter Topology

namespace TauCeti

/-- A continuous zero-free function on a sphere is bounded below there by a positive constant,
compactness of the sphere supplying the bound.

No hypothesis on the radius. At `ρ = 0` the sphere is the set of points at zero distance from
`a` — the single point `a` when `E` is a metric space, but not in general, since the domain is
only assumed pseudometric. For `ρ < 0` it is empty, nothing is attained, and the bound holds
vacuously. -/
theorem exists_pos_le_norm_of_mem_sphere {E F : Type*} [PseudoMetricSpace E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} {a : E} {ρ : ℝ}
    (hcont : ContinuousOn f (sphere a ρ)) (hne : ∀ z ∈ sphere a ρ, f z ≠ 0) :
    ∃ δ > 0, ∀ z ∈ sphere a ρ, δ ≤ ‖f z‖ :=
  (isCompact_sphere a ρ).exists_forall_le' hcont.norm fun z hz => norm_pos_iff.mpr (hne z hz)

/-- **A function with no zero off the centre does not vanish identically there.** If `f` is
nonzero at every point of an open ball of positive radius other than its centre `a`, then `f`
has finite analytic order at `a`: were the order `⊤`, `f` would vanish on a whole
neighbourhood of `a`, and that neighbourhood meets the ball away from `a`.

Nothing is assumed about `f a`, which may or may not be zero, nor about analyticity of `f`. -/
theorem analyticOrderAt_ne_top_of_forall_ne_zero {f : ℂ → ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hzf : ∀ z ∈ ball a ρ, z ≠ a → f z ≠ 0) : analyticOrderAt f a ≠ ⊤ := by
  intro hev
  rw [analyticOrderAt_eq_top] at hev
  obtain ⟨ε, hε, hbl⟩ := Metric.eventually_nhds_iff.mp hev
  set t : ℝ := min ε ρ / 2 with ht_def
  have ht0 : 0 < t := by rw [ht_def]; exact half_pos (lt_min hε hρ)
  have htε : t < ε := by have h := min_le_left ε ρ; rw [ht_def]; linarith
  have htρ : t < ρ := by have h := min_le_right ε ρ; rw [ht_def] at ht0 ⊢; linarith
  have hdist : dist (a + (t : ℂ)) a = t := by simp [dist_eq_norm, abs_of_pos ht0]
  refine hzf (a + (t : ℂ)) ?_ ?_ (hbl ?_)
  · simp only [mem_ball, hdist]; exact htρ
  · simp only [ne_eq, add_eq_left, Complex.ofReal_eq_zero]; exact ht0.ne'
  · rw [hdist]; exact htε

/-- **A function whose zeros are confined to a finite set has finite order.** If every zero of `f`
in an open set `U` lies in a finite set `S`, then `f` does not vanish identically near any point of
`U`, so `analyticOrderAt f z ≠ ⊤` there.

The point `z` itself is allowed to be a zero — indeed to lie in `S` — since vanishing identically
near `z` would force a whole punctured neighbourhood of zeros, of which all but finitely many are
outside `S`. This is the finite-set form of
`TauCeti.analyticOrderAt_ne_top_of_forall_ne_zero`, and reduces to it on a small enough ball. -/
theorem analyticOrderAt_ne_top_of_zeros_subset {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hzeros : ∀ w ∈ U, f w = 0 → w ∈ S) :
    analyticOrderAt f z ≠ ⊤ := by
  -- Deleting `z`, the finite set `S` is closed and misses `z`, so `U` minus it is an open
  -- neighbourhood of `z`; any ball inside it has no zero of `f` off its centre.
  have hopen : IsOpen (U ∩ ((S : Set ℂ) \ {z})ᶜ) :=
    hU.inter (S.finite_toSet.sdiff).isClosed.isOpen_compl
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen z ⟨hz, by simp⟩
  exact analyticOrderAt_ne_top_of_forall_ne_zero hρ fun w hw hwz hw0 =>
    (hball hw).2 ⟨hzeros w (hball hw).1 hw0, hwz⟩

/-- **An analytic function somewhere nonzero has finitely many zeros in a compact.** If `f` is
analytic on a neighbourhood of a preconnected set `U` and nonzero at some point of `U`, then
every compact subset of `U` contains only finitely many zeros of `f`: the zeros are isolated, so
the complement of the zero set is codiscrete within `U`, and a compact meets the complement of a
codiscrete set in a finite set.

Generalized from the modular-form-specific finiteness of the AINTLIB `LeanModularForms`
valence-formula development (`ForMathlib/ValenceFormula/PVChain/ResidueSideInfra.lean`) to
arbitrary analytic functions on a preconnected set. -/
theorem finite_setOfPred_eq_zero_of_isCompact {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U K : Set 𝕜} {x : 𝕜}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U) (hx : x ∈ U) (hfx : f x ≠ 0)
    (hK : IsCompact K) (hKU : K ⊆ U) : {z ∈ K | f z = 0}.Finite := by
  have hcod : f ⁻¹' {0}ᶜ ∈ Filter.codiscreteWithin K :=
    Filter.codiscreteWithin_mono hKU
      (hf.preimage_zero_mem_codiscreteWithin hfx hx ⟨⟨x, hx⟩, hU⟩)
  exact (hK.finite_sdiff_of_mem_codiscreteWithin hcod).subset fun z hz =>
    ⟨hz.1, by simpa using hz.2⟩

end TauCeti
