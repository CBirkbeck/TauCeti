/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Continuity for restricted actions

This file records generic transfer instances for actions whose pointwise orbit maps are
continuous. A submonoid, and hence a subgroup, inherits `ContinuousConstSMul` from an ambient
scalar action, and the orbit space of a second-countable space inherits second countability.
-/

public section

namespace TauCeti

namespace Submonoid

/-- A submonoid inherits continuity in the point from an ambient continuous action. -/
@[to_additive AddSubmonoid.continuousConstVAdd
/-- An additive submonoid inherits continuity in the point from an ambient continuous additive
action. -/]
instance continuousConstSMul {M X : Type*} [MulOneClass M] [TopologicalSpace X] [SMul M X]
    [ContinuousConstSMul M X] (S : Submonoid M) : ContinuousConstSMul S X :=
  ⟨fun g => by
    simpa only [Submonoid.smul_def] using continuous_const_smul (g : M)⟩

end Submonoid

namespace Subgroup

/-- A subgroup inherits continuity in the point from an ambient continuous action. -/
instance continuousConstSMul {G X : Type*} [Group G] [TopologicalSpace X] [SMul G X]
    [ContinuousConstSMul G X] (S : Subgroup G) : ContinuousConstSMul S X :=
  TauCeti.Submonoid.continuousConstSMul S.toSubmonoid

end Subgroup

namespace MulAction

/-- The orbit space of a second-countable space by a continuous action is second countable.

The quotient map `X → Quotient (orbitRel G X)` is open for any action by continuous maps, so a
countable basis of `X` pushes forward to a countable basis of the quotient. Note that no
separation or discreteness hypothesis is needed: openness of the quotient map is what carries
second countability, not properness of the action. -/
instance secondCountableTopology_orbitRel {G X : Type*} [Group G] [MulAction G X]
    [TopologicalSpace X] [SecondCountableTopology X] [ContinuousConstSMul G X] :
    SecondCountableTopology (Quotient (MulAction.orbitRel G X)) :=
  TopologicalSpace.Quotient.secondCountableTopology
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap

end MulAction

end TauCeti
