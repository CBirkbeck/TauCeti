/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.UniformRing

/-!
# The completion of a complete separated ring is itself

`UniformSpace.Completion.selfRingEquiv`: for a complete Hausdorff topological ring `S`, the
canonical map `S →+* UniformSpace.Completion S` is a ring isomorphism. The inverse is
`UniformSpace.Completion.extensionHom` of the identity; the two composites are the identity
by `extensionHom_coe` on the dense range of the coercion.

The declarations live in the root `UniformSpace.Completion` namespace they extend, following
this repository's convention for lemmas about external types.
-/

public section

namespace UniformSpace.Completion

variable (S : Type*) [Ring S] [UniformSpace S] [IsTopologicalRing S] [IsUniformAddGroup S]
  [CompleteSpace S] [T0Space S]

/-- For a complete Hausdorff topological ring, the coercion into the completion is a ring
isomorphism, with inverse the extension of the identity. -/
noncomputable def selfRingEquiv : UniformSpace.Completion S ≃+* S :=
  RingEquiv.ofRingHom (extensionHom (RingHom.id S) continuous_id) coeRingHom
    (RingHom.ext fun a ↦ extensionHom_coe (RingHom.id S) continuous_id a)
    (by
      refine RingHom.ext (congrFun ?_)
      refine UniformSpace.Completion.ext
        ((UniformSpace.Completion.continuous_coe S).comp
          UniformSpace.Completion.continuous_extension) continuous_id fun a ↦ ?_
      simp only [RingHom.coe_comp, RingHom.id_apply, Function.comp_apply,
        UniformSpace.Completion.extensionHom_coe]
      rfl)

@[simp]
theorem selfRingEquiv_coe (a : S) : selfRingEquiv S (a : UniformSpace.Completion S) = a :=
  extensionHom_coe (RingHom.id S) continuous_id a

@[simp]
theorem selfRingEquiv_symm_apply (a : S) :
    (selfRingEquiv S).symm a = (a : UniformSpace.Completion S) := (rfl)

end UniformSpace.Completion
