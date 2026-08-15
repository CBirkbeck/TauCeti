/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality of stabilisers under the two standard transports

A count defined through a point stabiliser is useful only alongside the rules for moving it.
Two such rules are recorded here, both consequences of Mathlib machinery rather than new
mathematics, and both stated for `Nat.card` because that is the form a numerical invariant of
an orbit is wanted in.

*Along an orbit* the stabiliser order does not change: related points have conjugate
stabilisers, by `MulAction.stabilizerEquivStabilizerOfOrbitRel`.

*Along a quotient* it divides: if a normal `N` and the induced `G ⧸ N`-action are compatible at
the point in question — which makes every element of `N` fix that point, though not necessarily
any other — then the quotient map restricts to a surjection of its stabiliser onto the
`G ⧸ N` one with kernel `N`, so the `G`-order is `Nat.card N` times the `G ⧸ N`-order.

## Main results

* `TauCeti.card_stabilizer_of_orbitRel`: the stabiliser order is an invariant of the orbit,
  with `TauCeti.card_stabilizer_smul` the translate-presented corollary.
* `TauCeti.card_stabilizer_quotient`: the stabiliser order divides by `Nat.card N` on passing
  to `G ⧸ N`.
-/

public section

namespace TauCeti

variable {G α : Type*} [Group G] [MulAction G α]

/-- **The order of a stabiliser is constant along an orbit**: points related by the orbit
relation have conjugate stabilisers, hence stabilisers of equal cardinality.

This is what lets a count defined through a point stabiliser — the order `e_P` of an elliptic
point of a Fuchsian group, say — be read as an invariant of the orbit. It holds with no
finiteness hypothesis: for an infinite stabiliser both sides are `0`, by `Nat.card`'s convention.

Not `@[simp]`: whether `Nat.card (stabilizer G a)` is in normal form depends on the action,
since a `simp` lemma for the particular `•` can rewrite inside it. -/
theorem card_stabilizer_of_orbitRel {a b : α} (h : MulAction.orbitRel G α a b) :
    Nat.card (MulAction.stabilizer G a) = Nat.card (MulAction.stabilizer G b) :=
  Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv

/-- The orbit invariance of `card_stabilizer_of_orbitRel` in the form wanted when the second
point is presented as a translate of the first. -/
theorem card_stabilizer_smul (g : G) (a : α) :
    Nat.card (MulAction.stabilizer G (g • a)) = Nat.card (MulAction.stabilizer G a) :=
  card_stabilizer_of_orbitRel ⟨g, rfl⟩

/-- **Passing to a quotient group divides stabiliser orders by the subgroup**: if `N` is normal
and the `G ⧸ N`-action agrees with the `G`-action along `QuotientGroup.mk` *at the point `a`*,
then the stabiliser of `a` in `G` is `Nat.card N` times its stabiliser in `G ⧸ N`.

Compatibility is asked for only at `a`, not globally, since that is all the count needs; a caller
holding the global statement supplies `fun g ↦ h g a`.

The compatibility hypothesis makes every element of `N` fix `a`, so `N ≤ stabilizer G a`, and
the quotient map restricts to a surjection of that stabiliser onto the `G ⧸ N` one with kernel
`N`; the count is then Lagrange. This is the step from a matrix-group stabiliser order to the
projective one — the elliptic orders `e_P` of a Fuchsian group are the `PSL` counts, half the
`SL` counts. -/
theorem card_stabilizer_quotient (N : Subgroup G) [N.Normal] [MulAction (G ⧸ N) α] (a : α)
    (hcompat : ∀ g : G, (QuotientGroup.mk g : G ⧸ N) • a = g • a) :
    Nat.card (MulAction.stabilizer G a) =
      Nat.card N * Nat.card (MulAction.stabilizer (G ⧸ N) a) := by
  have hle : N ≤ MulAction.stabilizer G a := fun n hn ↦
    (hcompat n).symm.trans <| by rw [(QuotientGroup.eq_one_iff n).mpr hn, one_smul]
  let φ : MulAction.stabilizer G a →* MulAction.stabilizer (G ⧸ N) a :=
    ((QuotientGroup.mk' N).comp (MulAction.stabilizer G a).subtype).codRestrict _ fun g ↦
      (hcompat _).trans g.2
  have hsurj : Function.Surjective φ := fun ⟨q, hq⟩ ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨g, (hcompat g).symm.trans hq⟩, rfl⟩
  -- `g` is in the kernel exactly when its image is `1` in `G ⧸ N`, i.e. when `g` lies in `N`
  have hker : φ.ker = N.subgroupOf (MulAction.stabilizer G a) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, ← hker, mul_comm]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup _

end TauCeti

end
