/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Bases

/-!
# A topological group with countably generated neighbourhoods of the identity is first countable

`FirstCountableTopology` asks every point's neighbourhood filter to be countably generated. In a
topological group it is enough to ask it at the identity: translation is a homeomorphism, so
`𝓝 a` is the image of `𝓝 1` under it, and the image of a countably generated filter is countably
generated.

This matters because countable generation at the identity is what the *proofs* in this area
assume — Henkel's open mapping theorem and
`NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup` both state it that way — whereas
`FirstCountableTopology` is the class **Mathlib's own instances are keyed on**. Without the bridge
the two do not meet: `(𝓝 (0 : ι → G)).IsCountablyGenerated` for a product, say, does not follow
from countable generation at `0` in `G`, because `𝓝` on a `Pi` type is not syntactically a
`Filter.pi` and `Filter.pi.isCountablyGenerated` never fires. With this instance the product,
subtype and additive-quotient forms all resolve.

Mathlib records the class-level consequences (`Subtype.firstCountableTopology`, the binary product,
…) but has no group-theoretic route *into* the class; `Mathlib/Topology/Bases.lean` carries a
standing "more fine grained instances for `FirstCountableTopology`" note where this would sit.

## Main results

* `IsTopologicalGroup.toFirstCountableTopology`, with its additive form
  `IsTopologicalAddGroup.toFirstCountableTopology`.
-/

namespace TauCeti

open Filter Topology

public section

/-- **A topological group whose identity has countably generated neighbourhoods is first
countable.** Left translation by `a` is a homeomorphism carrying `𝓝 1` to `𝓝 a`, and
`Filter.map` preserves countable generation.

Only the identity is assumed, because that is the form the surrounding theory states — see the
module docstring. -/
@[to_additive IsTopologicalAddGroup.toFirstCountableTopology]
instance IsTopologicalGroup.toFirstCountableTopology {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [(𝓝 (1 : G)).IsCountablyGenerated] : FirstCountableTopology G :=
  ⟨fun a ↦ by rw [← map_mul_left_nhds_one a]; infer_instance⟩

end

end TauCeti
