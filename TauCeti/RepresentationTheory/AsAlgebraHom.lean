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
arbitrary, and nothing is asked of `2` in `k` at all: the hypothesis is that doubling is injective
on `V`, taken as an explicit assumption rather than read off the scalars. So this covers
torsion-free modules over `ℤ`, where `2` is not a unit, and equally modules over a ring with zero
divisors whose additive group has no `2`-torsion.

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
theorem asAlgebraHom_eq_zero_of_mul_single_eq_neg
    (h2inj : Function.Injective fun w : V ↦ (2 : ℕ) • w)
    (ρ : Representation k G V) {a : MonoidAlgebra k G} {g : G} {v : V} (hfix : ρ g v = v)
    (hneg : a * MonoidAlgebra.single g 1 = -a) :
    ρ.asAlgebraHom a v = 0 := by
  -- Absorbing `g` into `a` costs a sign but leaves `v` alone, so the value equals its negation
  have key : ρ.asAlgebraHom a v = -(ρ.asAlgebraHom a v) := by
    conv_lhs => rw [← hfix]
    rw [← Representation.asAlgebraHom_single_one ρ, ← Module.End.mul_apply, ← map_mul, hneg,
      map_neg, LinearMap.neg_apply]
  -- so doubling it agrees with doubling `0`, and doubling is injective
  refine h2inj ?_
  simp only [two_nsmul, add_zero]
  nth_rewrite 1 [key]
  exact neg_add_cancel _

end Representation
