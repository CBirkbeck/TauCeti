/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
-- Proof-only: `smulAddHom`, the `n • ·` homomorphism the zsmul case is read through.
import Mathlib.Algebra.Module.End

/-!
# A nonempty fiber of a group homomorphism is a copy of the kernel

Mathlib's `AddMonoidHom.fiberEquivKer` exhibits a nonempty fiber of `f` as a coset of `ker f`, in
the set-preimage form `f ⁻¹' {f a}`. Substituting the attained value puts the subtype form
`{a // f a = b}` a caller usually meets into that shape, and three consequences follow: the fiber
is counted, made finite, and a sum over it is reindexed as a sum over the kernel.

Finiteness is the one of the three that needs no preimage: an empty fiber is finite as well, so the
statement is available before any point of the fiber is known, which is what a caller quantifying
over all values of `f` wants.

The multiplication map `n • ·` of an additive commutative group is the case the counting arguments
for isogenies use: each of its nonempty fibers has as many elements as the `n`-torsion. Emptiness
is not excluded by fiat — `n • ·` need not be surjective — so a preimage is an argument, and it is
the only thing either statement asks for.

## Main results

* `AddMonoidHom.card_fiber_eq_card_ker` (and `MonoidHom.card_fiber_eq_card_ker`): a nonempty
  fiber has as many elements as the kernel.
* `AddMonoidHom.finite_fiber` (and `MonoidHom.finite_fiber`): every fiber is finite when the
  kernel is.
* `AddMonoidHom.sum_fiber_eq_sum_ker` (and `MonoidHom.prod_fiber_eq_prod_ker`): summing over a
  nonempty fiber is summing `a + t` over the kernel.
* `TauCeti.card_zsmul_fiber_eq_card_zsmul_eq_zero`: the same for `n • ·` on an additive commutative
  group, with the kernel written as the `n`-torsion.
-/

public section

/-- **A nonempty fiber has as many elements as the kernel.** -/
@[to_additive
/-- **A nonempty fiber has as many elements as the kernel.** -/]
theorem MonoidHom.card_fiber_eq_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    {b : H} {a : G} (ha : f a = b) :
    Nat.card {x : G // f x = b} = Nat.card f.ker := by
  subst ha
  exact Nat.card_congr (f.fiberEquivKer a)

/-- **Every fiber is finite when the kernel is.** The empty fiber is covered too, so no preimage
has to be produced first. -/
@[to_additive
/-- **Every fiber is finite when the kernel is.** The empty fiber is covered too, so no preimage
has to be produced first. -/]
theorem MonoidHom.finite_fiber {G H : Type*} [Group G] [Group H] (f : G →* H) [Finite f.ker]
    (b : H) : Finite {x : G // f x = b} := by
  rcases isEmpty_or_nonempty {x : G // f x = b} with _ | ⟨⟨a, ha⟩⟩
  · infer_instance
  · subst ha
    exact Finite.of_equiv _ (f.fiberEquivKer a).symm

/-- **A product over a nonempty fiber is a product over the kernel**, translated by any point of
the fiber. -/
@[to_additive
/-- **A sum over a nonempty fiber is a sum over the kernel**, translated by any point of the
fiber. -/]
theorem MonoidHom.prod_fiber_eq_prod_ker {G H : Type*} [CommGroup G] [Group H] (f : G →* H)
    {b : H} {a : G} (ha : f a = b) [Fintype {x : G // f x = b}] [Fintype f.ker] :
    (∏ x : {x : G // f x = b}, (x : G)) = ∏ t : f.ker, a * (t : G) := by
  subst ha
  -- `f ⁻¹' {f a}` and `{x // f x = f a}` are the same type, but only the latter carries the
  -- `Fintype` instance the statement supplies, so name it for the former.
  let _ : Fintype ↥(⇑f ⁻¹' {f a}) := inferInstanceAs (Fintype {x : G // f x = f a})
  exact Fintype.prod_equiv (f.fiberEquivKer a) _ _ fun x ↦ by
    simp

namespace TauCeti

/-- **A nonempty fiber of `n • ·` has as many elements as the `n`-torsion.** -/
theorem card_zsmul_fiber_eq_card_zsmul_eq_zero {G : Type*} [AddCommGroup G] {n : ℤ} {T P₀ : G}
    (hP₀ : n • P₀ = T) :
    Nat.card {P : G // n • P = T} = Nat.card {P : G // n • P = 0} :=
  ((smulAddHom ℤ G n).card_fiber_eq_card_ker hP₀).trans <|
    Nat.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by simp

end TauCeti

end
