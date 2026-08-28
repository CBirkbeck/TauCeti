/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.LeftCosetModule.Action

/-!
# Convolution of Hecke orbits

This file exposes the orbit-sum form of the Hecke ring's structure constants. If `D₁` first
moves a left coset `q` through its orbit and `D₂` then moves every resulting coset, the final
cosets occur with exactly the multiplicities in the convolution product `[D₁] * [D₂]`.

`LeftCosetModule.Action` proves this counting fact internally in order to construct the module
over the opposite Hecke ring. The two results here are the public interface needed by actions
defined as finite sums over coset representatives: the pointwise fibre cardinality and the
corresponding equality of formal orbit sums.

Vendored from the orbit-counting argument in the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/AbstractHeckeRing/Module.lean`, Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB>), on top of the Hecke-ring convolution stack vendored from
the in-review Mathlib PRs #41253, #41277 and #41328.

## Main results

* `LeftCosetModule.card_filter_smulOrbit_eq_multiplicity`: the fibre over one output coset has
  cardinality equal to Shimura's multiplicity.
* `LeftCosetModule.sum_smulOrbit_smulOrbit_eq_structureConstants`: the full iterated orbit sum is
  the multiplicity-weighted sum of the output orbits.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.4.
-/

public section

open DoubleCoset Subgroup
open scoped HeckeCosetModule Pointwise

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G}

namespace LeftCosetModule

open HeckeCoset

variable [IsHeckeTriple Δ H H] {R : Type*} [Semiring R]

open Classical in
/-- **An iterated orbit sum is the structure-constant-weighted sum of the output orbits.**
For basis double cosets `D₁`, `D₂` and a basis left coset `q`, the formal sum obtained by
first following the `D₁`-orbit and then the `D₂`-orbit equals the sum over all double cosets
`D`, weighted by the coefficient of `D` in `[D₁] * [D₂]`, of the `D`-orbit of `q`.

The statement lives in the free left-coset module, rather than after applying a particular
function to its basis. Consumers can therefore transport it through any linear map; this is the
form used to regroup slash-operator composites by their final right coset. -/
theorem sum_smulOrbit_smulOrbit_eq_structureConstants
    (D₁ D₂ : HeckeCoset Δ H H) (q : HeckeCoset Δ ⊥ H) :
    (∑ i ∈ smulOrbit H D₁.rep q.rep, ∑ j ∈ smulOrbit H D₂.rep i.rep,
        Finsupp.single j (1 : R) : LeftCosetModule Δ H R) =
      (HeckeCosetModule.structureConstants R H H H D₁.rep D₂.rep).sum fun D mD ↦
        ∑ x ∈ smulOrbit H D.rep q.rep, Finsupp.single x mD := by
  have haction :
      MulOpposite.op (HeckeCosetModule.single R D₁ 1 *
          HeckeCosetModule.single R D₂ 1) •
          (Finsupp.single q 1 : LeftCosetModule Δ H R) =
        MulOpposite.op (HeckeCosetModule.single R D₂ 1) •
          (MulOpposite.op (HeckeCosetModule.single R D₁ 1) •
            (Finsupp.single q 1 : LeftCosetModule Δ H R)) := by
    simpa only [MulOpposite.op_mul] using
      (mul_smul (MulOpposite.op (HeckeCosetModule.single R D₂ 1))
        (MulOpposite.op (HeckeCosetModule.single R D₁ 1))
        (Finsupp.single q 1 : LeftCosetModule Δ H R))
  have hnested :
      MulOpposite.op (HeckeCosetModule.single R D₂ 1) •
          (MulOpposite.op (HeckeCosetModule.single R D₁ 1) •
            (Finsupp.single q 1 : LeftCosetModule Δ H R)) =
        ∑ i ∈ smulOrbit H D₁.rep q.rep, ∑ j ∈ smulOrbit H D₂.rep i.rep,
          Finsupp.single j (1 : R) := by
    rw [single_smul_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [single_smul_single]
    simp only [one_mul]
  have hstructure :
      MulOpposite.op (HeckeCosetModule.structureConstants R H H H D₁.rep D₂.rep) •
          (Finsupp.single q 1 : LeftCosetModule Δ H R) =
        (HeckeCosetModule.structureConstants R H H H D₁.rep D₂.rep).sum fun D mD ↦
          ∑ x ∈ smulOrbit H D.rep q.rep, Finsupp.single x mD := by
    rw [smul_eq_sum]
    refine Finsupp.sum_congr fun D _ ↦ ?_
    rw [Finsupp.sum_single_index (by simp), one_mul]
  rw [HeckeCosetModule.single_mul_single, one_smul, one_smul, hstructure, hnested] at haction
  exact haction.symm

end LeftCosetModule

end
