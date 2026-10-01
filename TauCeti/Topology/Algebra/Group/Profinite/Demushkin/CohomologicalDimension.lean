/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomologicalDimension

/-!
# The cohomological dimension of a Demushkin group

A Demushkin group `G` has `H²(G, 𝔽_p)` one-dimensional, so `H²(G, 𝔽_p) ≠ 0` and the lower bound
`Hⁿ(G, 𝔽_p) ≠ 0 → n ≤ cd_p G` (`TauCeti.le_cohomologicalDimensionAt_of_nontrivial_cohomFp`) gives
`2 ≤ cd_p G`. This is the lower bound in Tate's theorem that an infinite Demushkin group has
`cd_p G = 2` (Serre's exposé, §9.1); the upper bound is the right exactness of `H²` on the finite
`𝔽_p[G]`-modules, which follows from the perfect duality on those modules through
`TauCeti.IsProP.cohomologicalDimensionAt_le_two_of_forall_dualityMap2_bijective`.

The hypothesis "infinite" is not needed for the lower bound: the finite Demushkin group `ℤ/2` has
`cd_2 (ℤ/2) = ⊤`.

## Main results

* `TauCeti.IsDemushkin.two_le_cohomologicalDimensionAt`: a Demushkin group has `2 ≤ cd_p G`.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.1.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- **A Demushkin group has `p`-cohomological dimension at least `2`**: its `H²(G, 𝔽_p)` is
one-dimensional, hence nonzero. -/
theorem IsDemushkin.two_le_cohomologicalDimensionAt (hG : IsDemushkin p G) :
    2 ≤ cohomologicalDimensionAt.{u} p G :=
  le_cohomologicalDimensionAt_of_nontrivial_cohomFp
    (Module.nontrivial_of_finrank_eq_succ hG.finrank_cohomFp_two)

end TauCeti
