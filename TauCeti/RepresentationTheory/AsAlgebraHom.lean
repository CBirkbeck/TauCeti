/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Group-algebra elements that annihilate a fixed vector

An element `a` of the group algebra `k[G]` acting through a representation `ρ` kills a vector `v`
as soon as two conditions meet: some `g` fixes `v`, and right multiplication by `g` negates `a`.
Then `ρ.asAlgebraHom a v` is its own negative, so it vanishes as soon as doubling is injective
on `V`.

That is the mechanism behind the column-antisymmetrizer vanishing arguments of
`TauCeti/RepresentationTheory/Symmetric/`, which are its consumers: the antisymmetrizer of a set of
indices absorbs each permutation of those indices up to its sign, so against a vector fixed by an
odd such permutation the two conditions hold and the action is zero.

Nothing here is specific to symmetric groups or to `ℚ`. The group, the module and the scalars are
arbitrary, and `2` is not required to be invertible in `k` — only to act injectively on `V`, which
is what `[IsCancelMulZero k]`, `[Module.IsTorsionFree k V]` and `[NeZero (2 : k)]` supply. In
particular this covers torsion-free modules over `ℤ`, where `2` is not a unit.

## Main results

* `Representation.asAlgebraHom_eq_zero_of_mul_single_eq_neg`: an algebra element negated by right
  multiplication by a group element fixing `v` annihilates `v`.
-/

public section

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- **An algebra element absorbed by a fixing group element, up to sign, annihilates the vector.**
If `g` fixes `v` and right multiplication by `single g 1` negates `a`, then `a` acts as zero
on `v`. -/
theorem asAlgebraHom_eq_zero_of_mul_single_eq_neg [IsCancelMulZero k]
    [Module.IsTorsionFree k V] [NeZero (2 : k)]
    (ρ : Representation k G V) {a : MonoidAlgebra k G} {g : G} {v : V} (hfix : ρ g v = v)
    (hneg : a * MonoidAlgebra.single g 1 = -a) :
    ρ.asAlgebraHom a v = 0 := by
  -- Absorbing `g` into `a` costs a sign but leaves `v` alone, so the value equals its negation
  have key : ρ.asAlgebraHom a v = -(ρ.asAlgebraHom a v) := by
    conv_lhs => rw [← hfix]
    rw [← Representation.asAlgebraHom_single_one ρ, ← Module.End.mul_apply, ← map_mul, hneg,
      map_neg, LinearMap.neg_apply]
  have h2 : (2 : k) • ρ.asAlgebraHom a v = 0 := by
    rw [two_smul]
    nth_rewrite 2 [key]
    exact add_neg_cancel _
  -- and doubling is injective, so a value equal to its own negation is zero
  exact (smul_eq_zero.mp h2).resolve_left (NeZero.ne _)

end Representation
