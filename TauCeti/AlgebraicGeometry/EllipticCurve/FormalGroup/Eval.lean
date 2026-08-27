/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Inverse
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

/-- The value of the unit part differs from `1` by an element of `I`: its constant coefficient is
`1`, and every other monomial carries a factor of the parameter. -/
theorem formalUEval_sub_one_mem {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    W.formalUEval t - 1 ∈ I := by
  have hcont : Continuous ⇑(RingHom.id O) := by simpa using continuous_id
  have hEp : PowerSeries.HasEval t := isTopologicallyNilpotent_of_mem_of_isAdic hI ht
  have hE : MvPowerSeries.HasEval (fun _ : Unit ↦ t) := PowerSeries.hasEval hEp
  have key := MvPowerSeries.eval₂_mem_pow (k := 1) hcont hE hI (by simpa using ht)
    (W.formalU - 1) (by
      rw [show MvPowerSeries.constantCoeff (W.formalU - 1)
          = constantCoeff (W.formalU - 1) from rfl]
      simp [W.constantCoeff_formalU])
  -- `eval₂` is additive only through `eval₂Hom`, which needs the continuity and `HasEval` data.
  have hsplit : eval₂ (RingHom.id O) t (W.formalU - 1) = W.formalUEval t - 1 := by
    have h := map_sub (PowerSeries.eval₂Hom (S := O) hcont hEp) W.formalU 1
    rw [map_one] at h
    simpa [formalUEval, PowerSeries.coe_eval₂Hom] using h
  rw [← hsplit]
  simpa [eval₂] using key

/-- **The factorisation `w(t) = t ^ 3 * u(t)`** at a parameter, from the corresponding
factorisation `formalW_eq_X_pow_mul_formalU` of the series. -/
theorem formalWEval_eq_cube_mul {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    W.formalWEval t = t ^ 3 * W.formalUEval t := by
  have hcont : Continuous ⇑(RingHom.id O) := by simpa using continuous_id
  have hE : PowerSeries.HasEval t := isTopologicallyNilpotent_of_mem_of_isAdic hI ht
  have h := congrArg (PowerSeries.eval₂Hom (S := O) hcont hE) W.formalW_eq_X_pow_mul_formalU
  rw [map_mul, map_pow] at h
  simpa [formalWEval, formalUEval, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X] using h

/-- The value of the unit part is a unit, when `I` lies in the Jacobson radical — as it does for a
local ring's maximal ideal, or for the ideal of definition of a complete adic ring. -/
theorem isUnit_formalUEval {I : Ideal O} (hI : IsAdic I) (hJ : I ≤ Ideal.jacobson ⊥) {t : O}
    (ht : t ∈ I) : IsUnit (W.formalUEval t) :=
  Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJ (W.formalUEval_sub_one_mem hI ht))

/-! ### The inverse-side evaluations

Note which series these evaluate. The source's `uSeries` is this repository's
`formalInverseDenom`, **not** `formalU`; `formalU` is the source's `vSeries`, evaluated above as
`formalUEval`. Both are `PowerSeries O`, so pairing an evaluation with the wrong one would compile.
-/

/-- The value of the formal inverse's denominator `1 - a₁ z - a₃ w(z)` at a parameter. -/
noncomputable def formalInverseDenomEval (t : O) : O :=
  eval₂ (RingHom.id O) t W.formalInverseDenom

/-- The value at a parameter of the power-series inverse of `formalInverseDenom`. -/
noncomputable def formalInverseDenomInvEval (t : O) : O :=
  eval₂ (RingHom.id O) t (PowerSeries.invOfUnit W.formalInverseDenom 1)

/-- The value of the formal inverse `ι(z)` at a parameter. -/
noncomputable def formalInverseEval (t : O) : O := eval₂ (RingHom.id O) t W.formalInverse

/-- The denominator's value and the value of its series inverse multiply to `1`. -/
theorem formalInverseDenomEval_mul_inv {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    W.formalInverseDenomEval t * W.formalInverseDenomInvEval t = 1 := by
  have hcont : Continuous ⇑(RingHom.id O) := by simpa using continuous_id
  have hEp : PowerSeries.HasEval t := isTopologicallyNilpotent_of_mem_of_isAdic hI ht
  have h := congrArg (PowerSeries.eval₂Hom (S := O) hcont hEp)
    W.mul_invOfUnit_formalInverseDenom
  rw [map_mul, map_one] at h
  simpa [formalInverseDenomEval, formalInverseDenomInvEval, PowerSeries.coe_eval₂Hom] using h

/-- The denominator's value at a parameter is a unit. -/
theorem isUnit_formalInverseDenomEval {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    IsUnit (W.formalInverseDenomEval t) :=
  IsUnit.of_mul_eq_one _ (W.formalInverseDenomEval_mul_inv hI ht)

/-- The formal inverse maps a parameter of `I` back into `I`: it vanishes at the origin. -/
theorem formalInverseEval_mem {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    W.formalInverseEval t ∈ I := by
  have hcont : Continuous ⇑(RingHom.id O) := by simpa using continuous_id
  have hE : MvPowerSeries.HasEval (fun _ : Unit ↦ t) :=
    PowerSeries.hasEval (isTopologicallyNilpotent_of_mem_of_isAdic hI ht)
  have key := MvPowerSeries.eval₂_mem_pow (k := 1) hcont hE hI (by simpa using ht)
    W.formalInverse (by
      rw [show MvPowerSeries.constantCoeff W.formalInverse
          = constantCoeff W.formalInverse from rfl, W.constantCoeff_formalInverse]
      exact zero_mem _)
  simpa [formalInverseEval, eval₂] using key

/-- **The defining formula for the denominator's value**: `1 - a₁ t - a₃ w(t)`. -/
theorem formalInverseDenomEval_eq {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    W.formalInverseDenomEval t = 1 - W.a₁ * t - W.a₃ * W.formalWEval t := by
  have hcont : Continuous ⇑(RingHom.id O) := by simpa using continuous_id
  have hEp : PowerSeries.HasEval t := isTopologicallyNilpotent_of_mem_of_isAdic hI ht
  have h := congrArg (PowerSeries.eval₂Hom (S := O) hcont hEp) W.formalInverseDenom_def
  rw [map_sub, map_sub, map_one, map_mul, map_mul] at h
  simpa [formalInverseDenomEval, formalWEval, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C,
    PowerSeries.eval₂_X] using h

/-- **The defining formula for the formal inverse's value**: `ι(t) = -t / (1 - a₁ t - a₃ w(t))`,
written through the series inverse of the denominator. -/
theorem formalInverseEval_eq {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    W.formalInverseEval t = -(t * W.formalInverseDenomInvEval t) := by
  have hcont : Continuous ⇑(RingHom.id O) := by simpa using continuous_id
  have hEp : PowerSeries.HasEval t := isTopologicallyNilpotent_of_mem_of_isAdic hI ht
  have h := congrArg (PowerSeries.eval₂Hom (S := O) hcont hEp) W.formalInverse_def
  rw [map_neg, map_mul] at h
  simpa [formalInverseEval, formalInverseDenomInvEval, PowerSeries.coe_eval₂Hom,
    PowerSeries.eval₂_X] using h

end WeierstrassCurve
