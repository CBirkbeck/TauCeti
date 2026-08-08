/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.HungerbuhlerWasem
public import TauCeti.Analysis.Contour.Residue.LogDeriv

import TauCeti.Analysis.Contour.Argument.Principle

/-!
# The argument principle for a cycle running through the zeros

The argument principle in the form that tolerates zeros and poles **on** the contour. For `f`
whose zeros and poles in an open `U` all lie in a finite `S ⊆ U`, and a closed piecewise-`C¹`
*immersion* `γ` null-homologous in `U` and based off `S`, the Cauchy principal value of the
logarithmic integral is

`p.v. ∮_γ f'/f = 2πi · Σ_{z ∈ S} n_z(γ) · ord_z f`,

with the generalized (non-integer) winding numbers as weights. Where
`TauCeti.Contour.argumentPrinciple_nullHomologous` requires `γ` to avoid `S` and produces an
ordinary integral, here `γ` may run through the points of `S` — a zero on the contour is a pole
of `f'/f` on the contour, so the integral exists only as a principal value, and the point
contributes its order weighted by a winding number that need not be an integer. In the standard
configuration — a positively oriented curve with a single smooth branch through the point — that
weight is `1/2`; in general the generalized winding number at such a point is the average of the
two ordinary winding numbers on either side of the branch, so any `k ± 1/2` occurs.

The proof is the Hungerbühler–Wasem residue theorem in its simple-pole regime
(`TauCeti.Contour.hungerbuhlerWasem_residueTheorem_of_simple_poles`) applied to `logDeriv f`,
whose residue at each point is the order of `f` there
(`TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt`). What that regime asks for, and what
this file supplies, is that `logDeriv f` has at worst a simple pole at each point of `S`: HW's
conditions (A′) and (B) are then automatic, so no regularity hypothesis beyond the immersion
survives into the statement. The bound is not an extra assumption on `f` but a fact about
logarithmic derivatives — `f'/f` has a simple pole at a zero or pole of `f` whatever the order
there — which is why the hypotheses below are those of the classical statement with the
avoidance dropped.

Immersion, rather than mere piecewise-`C¹` regularity, is what the principal value at an on-curve
singularity needs: the curve must leave the point at a definite speed for the excised integrals to
converge.

## Main results

* `TauCeti.Contour.neg_one_le_meromorphicOrderAt_logDeriv` — a logarithmic derivative has at
  worst a simple pole.
* `TauCeti.Contour.hasCauchyPV_logDeriv_nullHomologous` — the principal-value argument principle
  for a cycle through the zeros.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Set

namespace TauCeti.Contour

/-- **A logarithmic derivative has at worst a simple pole.** If `f` is meromorphic at `z₀`, of
whatever order, then `meromorphicOrderAt (logDeriv f) z₀ ≥ -1`.

Near `z₀` the logarithmic derivative splits as `n · (· − z₀)⁻¹ + logDeriv g` with `g` analytic and
non-vanishing (`TauCeti.Contour.logDeriv_eventuallyEq_principalPart`); *that first summand* has
order at least `-1`, being exactly `-1` when `n ≠ 0` and `⊤` when `n = 0`, where it is the zero
function; the second summand is analytic; so the order of the sum is at least `-1`.
Differentiating cannot make the pole worse than simple however deep the zero or pole of `f` is: a
zero of order `n` contributes `n/(z - z₀)`, whose order is `-1` irrespective of `n`.

For `logDeriv f` itself the order is exactly `-1` when `ord_{z₀} f ≠ 0` — the analytic tail cannot
cancel a nonzero principal coefficient — merely `≥ 0` when `ord_{z₀} f = 0`, where `f'/f = g'/g`
is analytic, and `⊤` when `f` vanishes identically near `z₀`, where `f'/f = deriv f / 0` vanishes
too. Only the last case is not covered by the splitting, and it is handled separately below.

Meromorphy is essential rather than bookkeeping: at an essential singularity the bound fails, the
logarithmic derivative of `z ↦ exp (-z⁻¹)` being `z ↦ (z ^ 2)⁻¹`, of order `-2` at `0`.

This is the hypothesis that puts the argument principle into the unconditional regime of the
Hungerbühler–Wasem residue theorem. -/
theorem neg_one_le_meromorphicOrderAt_logDeriv {f : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (logDeriv f) z₀ := by
  rcases eq_or_ne (meromorphicOrderAt f z₀) ⊤ with htop | hne
  · -- `f` vanishes on a punctured neighbourhood, so `logDeriv f = deriv f / f` vanishes there too.
    have hlog : meromorphicOrderAt (logDeriv f) z₀ = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff] at htop ⊢
      filter_upwards [htop] with z hz
      simp [logDeriv, hz]
    rw [hlog]
    exact le_top
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨g, hg_an, hg_ne, hgerm⟩ := logDeriv_eventuallyEq_principalPart hf hn.symm
  have hlogg_an : AnalyticAt ℂ (logDeriv g) z₀ := analyticAt_logDeriv_of_analyticAt hg_an hg_ne
  have hinv : MeromorphicAt (fun z => (z - z₀)⁻¹) z₀ := meromorphicAt_sub_inv z₀
  have hA : MeromorphicAt (fun z => (n : ℂ) * (z - z₀)⁻¹) z₀ :=
    analyticAt_const.meromorphicAt.mul hinv
  have hinv_order : meromorphicOrderAt (fun z : ℂ => (z - z₀)⁻¹) z₀ = ((-1 : ℤ) : WithTop ℤ) := by
    rw [show (fun z : ℂ => (z - z₀)⁻¹) = ((· - z₀) ^ (-1 : ℤ)) from
      funext fun z => (zpow_neg_one _).symm]
    exact meromorphicOrderAt_zpow_id_sub_const
  have hprincipal :
      ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z => (n : ℂ) * (z - z₀)⁻¹) z₀ := by
    rw [show (fun z => (n : ℂ) * (z - z₀)⁻¹)
        = (fun _ => (n : ℂ)) * (fun z : ℂ => (z - z₀)⁻¹) from rfl,
      meromorphicOrderAt_mul analyticAt_const.meromorphicAt hinv, hinv_order]
    exact le_add_of_nonneg_left analyticAt_const.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr hgerm,
    show (fun z => (n : ℂ) * (z - z₀)⁻¹ + logDeriv g z)
        = (fun z => (n : ℂ) * (z - z₀)⁻¹) + logDeriv g from rfl]
  exact le_trans (le_min hprincipal
    (le_trans (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ (0 : ℤ)))
      hlogg_an.meromorphicOrderAt_nonneg))
    (meromorphicOrderAt_add hA hlogg_an.meromorphicAt)

/-- **The argument principle for a cycle running through the zeros.** For `f` analytic and
non-vanishing on `U` off a finite `S ⊆ U`, meromorphic at each point of `S` of order `ord`, and a
closed piecewise-`C¹` immersion `γ` in `U`, null-homologous there and based off `S`,

`p.v. ∮_γ f'/f = 2πi · Σ_{z ∈ S} n_z(γ) · ord z`.

Unlike `TauCeti.Contour.argumentPrinciple_nullHomologous`, the curve is free to pass through the
points of `S`: where the order is nonzero `f'/f` then has a pole on the contour, the integral
exists only as a principal value, and the generalized winding number supplies the weight, which
need not be an integer — `1/2` in the standard configuration of a positively oriented curve with
a single smooth branch through the point. Only the basepoint `γ a` is required to avoid `S`, as
it is what the principal value is anchored at.

The order function is prescribed at every point of `S`; `S` may list regular non-vanishing points
of `f`, whose order is `0` and which therefore contribute nothing. -/
theorem hasCauchyPV_logDeriv_nullHomologous {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ} {ord : ℂ → ℤ}
    (hU : IsOpen U) (hSU : (S : Set ℂ) ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hord : ∀ s ∈ S, meromorphicOrderAt f s = (ord s : WithTop ℤ))
    {γ : ℝ → ℂ} {a b : ℝ} (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) (hγa : γ a ∉ (S : Set ℂ))
    (hnull : IsNullHomologous γ a b U) :
    HasCauchyPV γ a b (logDeriv f)
      (2 * (Real.pi : ℂ) * Complex.I * ∑ z ∈ S, windingNumber γ a b z * (ord z : ℂ)) := by
  -- Off `S` the function is analytic and non-vanishing, so its logarithmic derivative is
  -- holomorphic there; at a point of `S` it is meromorphic, being `deriv f / f`.
  have hdiff : DifferentiableOn ℂ (logDeriv f) (U \ (↑S : Set ℂ)) := fun z hz =>
    (analyticAt_logDeriv_of_analyticAt (hoff z hz.1 hz.2).1
      (hoff z hz.1 hz.2).2).differentiableAt.differentiableWithinAt
  have hmeroL : ∀ s ∈ S, MeromorphicAt (logDeriv f) s := fun s hs =>
    (hmero s hs).deriv.div (hmero s hs)
  -- `Res_s (f'/f) = ord_s f` at every point of `S`.
  have hsum : ∑ s ∈ S, windingNumber γ a b s * residue (logDeriv f) s
      = ∑ z ∈ S, windingNumber γ a b z * (ord z : ℂ) :=
    Finset.sum_congr rfl fun s hs => by
      rw [residue_logDeriv_eq_meromorphicOrderAt (hmero s hs) (hord s hs)]
  rw [← hsum]
  exact hungerbuhlerWasem_residueTheorem_of_simple_poles hU S γ a b hγ_imm hSU hclosed hγa hγU
    hdiff hmeroL hnull fun s hs =>
      neg_one_le_meromorphicOrderAt_logDeriv (hmero s hs)

end TauCeti.Contour

end
