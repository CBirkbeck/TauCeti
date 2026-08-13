/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.UniformSpace.Completion

/-!
# The completion of a complete separated ring is itself

`UniformSpace.Completion.selfRingEquiv`: for a complete Hausdorff topological ring `S`, the
extension of the identity is a ring isomorphism `UniformSpace.Completion S ≃+* S`. The ring
homomorphism is `UniformSpace.Completion.extensionHom`; its underlying function is the
uniform bijection `UniformCompletion.completeEquivSelf`, which supplies bijectivity.

The declarations live in the root `UniformSpace.Completion` namespace they extend, following
this repository's convention for lemmas about external types.
-/

public section

namespace UniformSpace.Completion

variable (S : Type*) [Ring S] [UniformSpace S] [IsTopologicalRing S] [IsUniformAddGroup S]
  [CompleteSpace S] [T0Space S]

/-- For a complete Hausdorff topological ring, the extension of the identity is a ring
isomorphism from the completion — bijective because it is the underlying map of the uniform
bijection `UniformCompletion.completeEquivSelf`. -/
noncomputable def selfRingEquiv : UniformSpace.Completion S ≃+* S :=
  RingEquiv.ofBijective (extensionHom (RingHom.id S) continuous_id)
    (UniformCompletion.completeEquivSelf (α := S)).bijective

@[simp]
theorem selfRingEquiv_coe (a : S) : selfRingEquiv S (a : UniformSpace.Completion S) = a :=
  extensionHom_coe (RingHom.id S) continuous_id a

end UniformSpace.Completion
