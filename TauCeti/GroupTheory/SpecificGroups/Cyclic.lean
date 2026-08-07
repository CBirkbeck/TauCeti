/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A group with two elements is `Multiplicative (ZMod 2)`

The computable isomorphism `G ≃* Multiplicative (ZMod 2)` for a group `G` exhausted by the
identity and one distinguished nonidentity element. Mathlib's cyclic-group machinery produces
such an isomorphism only noncomputably (through `IsCyclic` and a choice of generator); taking
the generator and the exhaustion as data keeps it computable, which is what
`TauCeti/AlgebraicGeometry/EllipticCurve/Aut.lean` needs for the automorphism group of an
elliptic curve with `j ∉ {0, 1728}`.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/GroupTheory/SpecificGroups/Cyclic.lean` at `d18b563029f3`, Apache 2.0, by
Kevin Buzzard and Claude).
-/

@[expose] public section

/-- A group `G` with exactly two elements — the identity `1` and a distinguished element `g ≠ 1`,
every element being equal to one of the two — is isomorphic to `Multiplicative (ZMod 2)`, via the
isomorphism sending `g` to `Multiplicative.ofAdd 1`. The generator `g` and the exhaustion `key` are
taken as explicit data (rather than a bare `Nat.card G = 2`) so the isomorphism is computable. -/
def mulEquivMultiplicativeZModTwo {G : Type*} [Group G] [DecidableEq G] (g : G) (hg : g ≠ 1)
    (key : ∀ x : G, x = 1 ∨ x = g) : G ≃* Multiplicative (ZMod 2) :=
  have hgg : g * g = 1 := (key (g * g)).resolve_right fun h ↦ hg (mul_eq_right.mp h)
  have keyM : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = .ofAdd 1 := by decide
  have hM1 : (.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by decide
  have hMM : (.ofAdd 1 : Multiplicative (ZMod 2)) * .ofAdd 1 = 1 := by decide
  { toFun x := if x = 1 then 1 else .ofAdd 1
    invFun x := if x = 1 then 1 else g
    left_inv x := by rcases key x <;> grind
    right_inv x := by rcases keyM x <;> grind
    map_mul' a b := by rcases key a <;> rcases key b <;> grind }

end
