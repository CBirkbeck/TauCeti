/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic

/-!
# A submodule of a topological module is a topological module

A submodule carries the subspace topology, and Mathlib already reaches `↥p` for two of the three
continuity classes that make it a module topology: `SMulMemClass.continuousSMul` gives the jointly
continuous action, and `Submodule.topologicalAddGroup` gives `ContinuousAdd` when the ambient
module is a topological *group*. The remaining two cases are what this file supplies, each at the
generality of its own class.

Neither is reachable by weakening: `ContinuousAdd` on an `AddCommMonoid` ambient is out of
`Submodule.topologicalAddGroup`'s reach, and the constant-scalar action needs **no topology on
`A`** — which is exactly the form `TauCeti.Huber.restrictedMvPowerSeriesSubmodule` takes, and the
reason `SMulMemClass.continuousSMul` does not cover it.

## Main results

* `Submodule.continuousAdd`: addition on `↥p` is continuous, asking only `ContinuousAdd` of the
  ambient module rather than a topological group structure.
* `Submodule.continuousConstSMul`: each scalar acts continuously on `↥p`, with no topology on the
  scalars.
-/

public section

namespace Submodule

variable {A M : Type*} [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M]

/-- **Addition on a submodule is continuous.** Mathlib has this for an `AddSubmonoid`, and for a
`Submodule` only through `Submodule.topologicalAddGroup`, which needs the ambient module to be a
topological group. A `ContinuousAdd` ambient is enough. -/
instance continuousAdd [ContinuousAdd M] (p : Submodule A M) : ContinuousAdd p :=
  inferInstanceAs (ContinuousAdd p.toAddSubmonoid)

/-- **Each scalar acts continuously on a submodule**, since it does so on the ambient module and
the action is the restriction of that one. -/
instance continuousConstSMul [ContinuousConstSMul A M] (p : Submodule A M) :
    ContinuousConstSMul A p :=
  Topology.IsInducing.subtypeVal.continuousConstSMul id rfl

end Submodule
