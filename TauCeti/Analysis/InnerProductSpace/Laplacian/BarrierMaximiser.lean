/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple

/-!
# The maximizer step shared by the lower-order weak maximum principles

Both lower-order weak maximum principles — for `-Δ + c` in
`TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple` and for
`-Δ - b·∇ + c` in `TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple` —
perturb a subsolution by a barrier, take a maximizer of the perturbation over the compact set, and
then argue that the frontier bound already holds at that maximizer. Only the last step is common:
the two differ in how they produce the maximizer and in which barrier they use.

This module holds that step, stated once for the operator `Δ + b·∇` with an arbitrary barrier. The
`-Δ + c` principle runs it at `b = 0` with the quadratic barrier `‖·‖²`.

It is a support module: it exists so the two principles can share a proof, not to add public API.
Both consumers import it *non-publicly*, so neither re-exports it, and nothing downstream of either
principle acquires `le_of_isMaxOn_add_smul` as part of its interface.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The maximizer step of the lower-order weak maximum principles.** At a maximizer `z` of
`f + ε • w` over `K`, where `f` is a subsolution of `Δ + b·∇` bounded by a nonnegative `m` on the
frontier and `w` is a barrier that is strictly positive under `Δ + b·∇` at `z`, the frontier bound
already holds at `z`.

Everything about `f`, `c` and the barrier is asked for at the single point `z`, and only when `z`
is interior: the frontier branch is the hypothesis `hbdry` outright. A caller holding the usual
`∀ x ∈ interior K` form instantiates it at `z`, as `fun h => hcd h`. -/
theorem le_of_isMaxOn_add_smul {K : Set E} {c f w : E → ℝ} {b : E → E} {m ε : ℝ} {z : E}
    (hm : 0 ≤ m) (hε : 0 < ε) (hcd : z ∈ interior K → ContDiffAt ℝ 2 f z)
    (hc : z ∈ interior K → 0 ≤ c z)
    (hsub : z ∈ interior K → c z * f z ≤ Δ f z + fderiv ℝ f z (b z))
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) (hzK : z ∈ K)
    (hwcd : z ∈ interior K → ContDiffAt ℝ 2 w z)
    (hwpos : z ∈ interior K → 0 < Δ w z + fderiv ℝ w z (b z))
    (hzmax : IsMaxOn (fun y => f y + ε • w y) K z) :
    f z ≤ m := by
  by_cases hzint : z ∈ interior K
  · -- Interior: `f z > m ≥ 0` makes `Δ f + ∇_b f` nonnegative, so the perturbed sum is strictly
    -- positive and `z` cannot be a local maximum.
    by_contra hn
    have hfz0 : 0 ≤ f z := hm.trans (not_le.mp hn).le
    have hLf0 : 0 ≤ Δ f z + fderiv ℝ f z (b z) :=
      (mul_nonneg (hc hzint) hfz0).trans (hsub hzint)
    have hpos : 0 < Δ (fun y => f y + ε • w y) z +
        fderiv ℝ (fun y => f y + ε • w y) z (b z) := by
      rw [laplacian_add_fderiv_add_const_smul f w (b z) ε z (hcd hzint) (hwcd hzint)]
      nlinarith [mul_pos hε (hwpos hzint)]
    exact not_isLocalMax_of_laplacian_add_fderiv_pos
      ((hcd hzint).add ((hwcd hzint).const_smul ε)) hpos
      (hzmax.isLocalMax (mem_interior_iff_mem_nhds.mp hzint))
  · exact hbdry ⟨subset_closure hzK, hzint⟩

end TauCeti

end

end
