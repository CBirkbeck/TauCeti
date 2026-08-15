/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The order of a stabiliser is an invariant of the orbit

Points of a single orbit have conjugate stabilisers, so their stabilisers are isomorphic and in
particular equinumerous. Mathlib supplies the isomorphism,
`MulAction.stabilizerEquivStabilizerOfOrbitRel`; what is recorded here is the cardinality
consequence, which is the form wanted whenever a numerical invariant is attached to an orbit
rather than to a chosen representative of it.

## Main results

* `TauCeti.card_stabilizer_smul`: `Nat.card` of the stabiliser is unchanged by moving the point
  along the action.
-/

public section

namespace TauCeti

variable {G α : Type*} [Group G] [MulAction G α]

/-- **The order of a stabiliser is constant along an orbit**: `g • a` and `a` have conjugate
stabilisers, hence stabilisers of equal cardinality.

This is what lets a count defined through a point stabiliser — the order `e_P` of an elliptic
point of a Fuchsian group, say — be read as an invariant of the orbit. It holds with no
finiteness hypothesis: for an infinite stabiliser both sides are `0`, by `Nat.card`'s convention.

Not `@[simp]`: whether `Nat.card (stabilizer G (g • a))` is in normal form depends on the action,
since a `simp` lemma for the particular `•` can rewrite inside it. -/
theorem card_stabilizer_smul (g : G) (a : α) :
    Nat.card (MulAction.stabilizer G (g • a)) = Nat.card (MulAction.stabilizer G a) :=
  Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel
    (⟨g, rfl⟩ : MulAction.orbitRel G α (g • a) a)).toEquiv

end TauCeti

end
