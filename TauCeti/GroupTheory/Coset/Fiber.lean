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
the set-preimage form `f ⁻¹' {f a}`, with the attained value written as a value of `f`. A caller
usually meets the fiber as the subtype `{a // f a = b}` instead, and holds `f a = b` separately;
`subtypeFiberEquivKer` is Mathlib's equivalence read in that form, so the substitution is made once
here rather than at each use. Three consequences follow from it: the fiber is counted, made finite,
and a sum over it is reindexed as a sum over the kernel.

Finiteness is the one of the three that needs no preimage: an empty fiber is finite as well, so the
statement is available before any point of the fiber is known, which is what a caller quantifying
over all values of `f` wants.

The multiplication map `n • ·` of an additive commutative group is the case the counting arguments
for isogenies use: each of its nonempty fibers has as many elements as the `n`-torsion. Emptiness
is not excluded by fiat — `n • ·` need not be surjective — so a preimage is an argument, and it is
the only thing either statement asks for.

## Main results

* `AddMonoidHom.subtypeFiberEquivKer` (and `MonoidHom.subtypeFiberEquivKer`): the fiber over an
  attained value, as a subtype, is equivalent to the kernel.
* `AddMonoidHom.card_fiber_eq_card_ker` (and `MonoidHom.card_fiber_eq_card_ker`): a nonempty
  fiber has as many elements as the kernel.
* `AddMonoidHom.finite_fiber` (and `MonoidHom.finite_fiber`): every fiber is finite when the
  kernel is.
* `AddMonoidHom.sum_fiber_eq_sum_ker` (and `MonoidHom.prod_fiber_eq_prod_ker`): summing over a
  nonempty fiber is summing `a + t` over the kernel.
* `TauCeti.card_zsmul_fiber_eq_card_zsmul_eq_zero`: the same for `n • ·` on an additive commutative
  group, with the kernel written as the `n`-torsion.

## Provenance

Generalized from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0)
pinned at `a302aeacd86053f9d5f991fbbf664e1cc1051d08`: `HasseWeil/HasseBound/WeilPairing/Fiber.lean`,
declarations `fiberEquivKer`, `fiber_finite` and `fiber_card_eq_ker_card`, and
`HasseWeil/HasseBound/WeilPairing/SigmaBridge.lean`, declaration `fiber_sum_eq_ker_sum`. There they
are stated for an endomorphism of the point group of an elliptic curve; here they hold of any
homomorphism of groups, the commutative hypothesis appearing only where an unordered product is
taken. The source builds its fiber equivalence by hand, where this one is Mathlib's
`fiberEquivKer` composed with the change of presentation.
-/

public section

/-- **A nonempty fiber is a copy of the kernel**, in the subtype form. Mathlib's
`MonoidHom.fiberEquivKer` is stated on the set preimage `f ⁻¹' {f a}`, with the attained value
written as a value of `f`; given `ha : f a = b` this is the same equivalence on `{x // f x = b}`,
so a consumer does not repeat the substitution. -/
@[to_additive
/-- **A nonempty fiber is a copy of the kernel**, in the subtype form. Mathlib's
`AddMonoidHom.fiberEquivKer` is stated on the set preimage `f ⁻¹' {f a}`, with the attained value
written as a value of `f`; given `ha : f a = b` this is the same equivalence on `{x // f x = b}`,
so a consumer does not repeat the substitution. -/]
def MonoidHom.subtypeFiberEquivKer {G H : Type*} [Group G] [Group H] (f : G →* H) {b : H} {a : G}
    (ha : f a = b) : {x : G // f x = b} ≃ f.ker :=
  (Equiv.subtypeEquivRight fun _ ↦ by simp [← ha]).trans (f.fiberEquivKer a)

/-- **A nonempty fiber has as many elements as the kernel.** -/
@[to_additive
/-- **A nonempty fiber has as many elements as the kernel.** -/]
theorem MonoidHom.card_fiber_eq_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    {b : H} {a : G} (ha : f a = b) :
    Nat.card {x : G // f x = b} = Nat.card f.ker :=
  Nat.card_congr (f.subtypeFiberEquivKer ha)

/-- **Every fiber is finite when the kernel is.** The empty fiber is covered too, so no preimage
has to be produced first. -/
@[to_additive
/-- **Every fiber is finite when the kernel is.** The empty fiber is covered too, so no preimage
has to be produced first. -/]
theorem MonoidHom.finite_fiber {G H : Type*} [Group G] [Group H] (f : G →* H) [Finite f.ker]
    (b : H) : Finite {x : G // f x = b} := by
  rcases isEmpty_or_nonempty {x : G // f x = b} with _ | ⟨⟨a, ha⟩⟩
  · infer_instance
  · exact Finite.of_equiv _ (f.subtypeFiberEquivKer ha).symm

/-- **A product over a nonempty fiber is a product over the kernel**, translated by any point of
the fiber. -/
@[to_additive
/-- **A sum over a nonempty fiber is a sum over the kernel**, translated by any point of the
fiber. -/]
theorem MonoidHom.prod_fiber_eq_prod_ker {G H : Type*} [CommGroup G] [Group H] (f : G →* H)
    {b : H} {a : G} (ha : f a = b) [Fintype {x : G // f x = b}] [Fintype f.ker] :
    (∏ x : {x : G // f x = b}, (x : G)) = ∏ t : f.ker, a * (t : G) :=
  Fintype.prod_equiv (f.subtypeFiberEquivKer ha) _ _ fun _ ↦ by
    simp [MonoidHom.subtypeFiberEquivKer]

namespace TauCeti

/-- **A nonempty fiber of `n • ·` has as many elements as the `n`-torsion.** -/
theorem card_zsmul_fiber_eq_card_zsmul_eq_zero {G : Type*} [AddCommGroup G] {n : ℤ} {T P₀ : G}
    (hP₀ : n • P₀ = T) :
    Nat.card {P : G // n • P = T} = Nat.card {P : G // n • P = 0} :=
  ((smulAddHom ℤ G n).card_fiber_eq_card_ker hP₀).trans <|
    Nat.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by simp

end TauCeti

end
