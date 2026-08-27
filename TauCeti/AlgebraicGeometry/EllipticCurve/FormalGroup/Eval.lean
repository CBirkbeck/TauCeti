/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.RingTheory.MvPowerSeries.Evaluation

/-!
# Evaluating the `w`-expansion at a parameter

For a Weierstrass curve `W` over a topological ring `O` whose topology is the `I`-adic one, the
`w`-expansion of `FormalGroup/WExpansion.lean` can be evaluated at a parameter `t ∈ I`. This file
provides that evaluation and its basic membership properties.

## Main definitions

* `WeierstrassCurve.formalWEval` : the value `w(t)` of the `w`-expansion at `t`.
* `WeierstrassCurve.formalUEval` : the value `u(t)` of its unit part `w(z) / z ^ 3`.

## Implementation notes

The evaluation is Mathlib's `PowerSeries.eval₂` at the identity ring hom. The adic hypothesis is
carried as an explicit `IsAdic I` argument rather than through a `WithIdeal` instance, matching
`MvPowerSeries.eval₂_mem_pow`, which these results call. `WithIdeal` would supply the topology
itself at `priority := 100`, so on a ring that already carries one — `ℤ_[p]`, whose topology comes
from its metric — the adic topology is shadowed and the results become inapplicable. `IsAdic` is
instead a *proposition about* the ambient topology, so it can be supplied for such a ring.

Names follow the series on this side rather than the source's: the evaluation of `formalW` is
`formalWEval`, and so on. The source's names do not transfer, because the source-to-repository map
is not order-preserving — the source's `uSeries` is this repository's `formalInverseDenom`, while
`formalU` is the source's `vSeries` — and every series here has the same type, so a mismatched
pairing would compile.
-/

public section

open PowerSeries

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O] (W : WeierstrassCurve O)

/-- The value of the `w`-expansion at a parameter. -/
noncomputable def formalWEval (t : O) : O := eval₂ (RingHom.id O) t W.formalW

/-- The value of the unit part `u(z) = w(z) / z ^ 3` at a parameter. -/
noncomputable def formalUEval (t : O) : O := eval₂ (RingHom.id O) t W.formalU

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- An element of an ideal defining the topology is topologically nilpotent. This is
`WithIdeal.isTopologicallyNilpotent_of_mem` transported along the equality of topologies that
`IsAdic` asserts, so that it applies to a ring carrying its topology by some other route. -/
theorem isTopologicallyNilpotent_of_mem_of_isAdic {I : Ideal O} (hI : IsAdic I) {t : O}
    (ht : t ∈ I) : IsTopologicallyNilpotent t := by
  suffices ∀ m : ℕ, ∃ n₀, ∀ n, n₀ ≤ n → t ^ n ∈ I ^ m by
    simpa [IsTopologicallyNilpotent, hI.hasBasis_nhds_zero.tendsto_right_iff]
  exact fun m ↦ ⟨m, fun n hn ↦ Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow ht _)⟩

/-- The value of the `w`-expansion at a parameter of `I` again lies in `I`: the expansion has
vanishing constant coefficient, and every other monomial carries a factor of the parameter. -/
theorem formalWEval_mem {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    W.formalWEval t ∈ I := by
  have hcont : Continuous ⇑(RingHom.id O) := by simpa using continuous_id
  have hE : MvPowerSeries.HasEval (fun _ : Unit ↦ t) :=
    PowerSeries.hasEval (isTopologicallyNilpotent_of_mem_of_isAdic hI ht)
  have key := MvPowerSeries.eval₂_mem_pow (k := 1) hcont hE hI (by simpa using ht) W.formalW (by
    rw [show MvPowerSeries.constantCoeff W.formalW = constantCoeff W.formalW from rfl,
      W.constantCoeff_formalW]
    exact zero_mem _)
  simpa [formalWEval, eval₂] using key

end WeierstrassCurve
