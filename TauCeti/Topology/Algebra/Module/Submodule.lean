/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic

/-!
# A submodule of a topological module is a topological module

Mathlib gives a submodule of a topological module its subspace topology, and records
`Submodule.topologicalAddGroup` for the case of an ambient topological *group*. The three
continuity classes that make the subspace topology a module topology are not instances, so
typeclass search cannot form a statement about `↥p` for `p : Submodule A M` unless the ambient
module is a group and only additive structure is wanted.

This file supplies them, at the generality of the classes themselves: an `AddCommMonoid` ambient
suffices, and each class is inherited separately.

## Main results

* `TauCeti.Submodule.continuousAdd`: addition on `↥p` is continuous.
* `TauCeti.Submodule.continuousConstSMul`: each scalar acts continuously on `↥p`.
* `TauCeti.Submodule.continuousSMul`: the action `A × ↥p → ↥p` is jointly continuous.
-/

public section

namespace TauCeti

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
  ⟨fun a ↦ ((continuous_const_smul a).comp continuous_subtype_val).subtype_mk _⟩

/-- **The scalar action on a submodule is jointly continuous.** With
`ContinuousSMul.continuousConstSMul` this subsumes `TauCeti.Submodule.continuousConstSMul`, which
is stated separately because it needs no topology on `A`. -/
instance continuousSMul [TopologicalSpace A] [ContinuousSMul A M] (p : Submodule A M) :
    ContinuousSMul A p :=
  ⟨(continuous_smul.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

end Submodule

end TauCeti
