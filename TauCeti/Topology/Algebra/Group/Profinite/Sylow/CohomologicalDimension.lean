/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.IndexNotDvd
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Basic

/-!
# The `p`-cohomological dimension of a profinite group is at most that of a Sylow subgroup

Let `G` be a profinite group, `p` a prime and `P` a Sylow pro-`p` subgroup of `G`. Then
`cd_p G ≤ cd_p P`. Every open subgroup of `G` containing `P` has index prime to `p`
(`TauCeti.IsProPSylow.not_dvd_index_of_le`), so restriction from `G` to `P` is injective on the
cohomology of every discrete `p`-primary torsion `G`-module in every positive degree, and a
vanishing statement for `P` transfers to `G`. This is one half of the equality `cd_p G = cd_p P`
(Serre, *Galois Cohomology*, I §3.3, Cor. 1 to Prop. 14; NSW (3.3.6)). The other half,
`cd_p P ≤ cd_p G`, is the monotonicity of `cd_p` in a closed subgroup, that is Shapiro's lemma for
the closed subgroup `P`, and is not proved here.

## Main results

* `TauCeti.CohomologicalDimensionLE.of_isProPSylow`: the vanishing predicate `cd_p P ≤ n` for a
  Sylow pro-`p` subgroup `P` implies `cd_p G ≤ n`.
* `TauCeti.IsProPSylow.cohomologicalDimensionAt_le`: **`cd_p G ≤ cd_p P`** for a Sylow pro-`p`
  subgroup `P` of a profinite group `G`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.3, Cor. 1 to Prop. 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.6).
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {P : Subgroup G}

/-- **`cd_p G ≤ cd_p P` for a Sylow pro-`p` subgroup `P`**, as the vanishing predicate: for a
Sylow pro-`p` subgroup `P` of a profinite group `G`, `CohomologicalDimensionLE p P n` implies
`CohomologicalDimensionLE p G n`. -/
theorem CohomologicalDimensionLE.of_isProPSylow (hP : IsProPSylow p P) {n : ℕ}
    (h : CohomologicalDimensionLE.{v} p P n) : CohomologicalDimensionLE.{v} p G n :=
  h.of_isClosed_of_forall_not_dvd_index Fact.out hP.isClosed hP.not_dvd_index_of_le

/-- **`cd_p G ≤ cd_p P` for a Sylow pro-`p` subgroup `P` of a profinite group `G`** (Serre,
*Galois Cohomology*, I §3.3, Cor. 1 to Prop. 14): the `p`-cohomological dimension of `G` is at most
that of any of its Sylow pro-`p` subgroups. -/
theorem IsProPSylow.cohomologicalDimensionAt_le (hP : IsProPSylow p P) :
    cohomologicalDimensionAt.{v} p G ≤ cohomologicalDimensionAt.{v} p P :=
  cohomologicalDimensionAt_le_of_isClosed_of_forall_not_dvd_index Fact.out hP.isClosed
    hP.not_dvd_index_of_le

end TauCeti
