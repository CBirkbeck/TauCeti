/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-!
# The canonical topology on a finitely generated module over a Tate ring

Wedhorn's Remark 6.19: let `A` be a Tate ring, `A₀` a ring of definition, `ϖ ∈ A₀` a
pseudouniformiser, and `M₀` an `A₀`-submodule of an `A`-module `M` with `A · M₀ = M`. Then the
family `ϖⁿ • M₀` is a fundamental system of open neighbourhoods of `0` for the topology of
Wedhorn's Proposition 6.18(1).

This file exhibits that family as a `SubmodulesBasis`, which is Mathlib's machinery for turning
such a family into a topology; `SubmodulesBasis.topology` and `.nonarchimedean` then apply.

## Main results

* `TauCeti.Huber.PairOfDefinition.exists_pow_smul_mem`: a power of `ϖ` carries any element of
  `M` into `M₀`. This is where `A · M₀ = M` is spent.
* `TauCeti.Huber.PairOfDefinition.fgFamily_submodulesBasis`: the family is a `SubmodulesBasis`.

## Implementation notes

The neighbourhoods are `A₀`-submodules, not `A`-submodules, so `SubmodulesBasis` is instantiated
at `R := P.ringOfDefinition`: `M` carries its `A₀`-module structure by restriction of scalars
along `A₀ → A`, which typeclass inference supplies unaided.

The family is `ϖⁿ • M₀` rather than `Iⁿ • M₀` for the ideal of definition `I`. That is Wedhorn's
own indexing, and it is forced: the `smul` condition needs `Iⁿ · ϖᵏ` to contain a neighbourhood
of `0`, which holds only when `I = ϖA₀` — exactly the hypothesis Remark 6.19 runs under.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.18 and
  Remark 6.19.
-/

public section

open Filter
open scoped Topology Pointwise

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M]

omit [IsTopologicalRing A] in
/-- **Wedhorn's Remark 6.19 family**: the `A₀`-submodules `ϖⁿ • M₀` of `M`. -/
def fgFamily (P : PairOfDefinition A) {s : A} (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (n : ℕ) : Submodule P.ringOfDefinition M :=
  ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n) • M₀

omit [IsTopologicalRing A] in
/-- The family is antitone, which is the `inter` half of `SubmodulesBasis`. -/
theorem fgFamily_antitone (P : PairOfDefinition A) {s : A} (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) : Antitone (P.fgFamily hs0 M₀) := by
  intro i j hij
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨((⟨s, hs0⟩ : P.ringOfDefinition) ^ d) • y, M₀.smul_mem _ hy, ?_⟩
  simp [smul_smul, ← pow_add, Nat.add_comm]

end TauCeti.Huber.PairOfDefinition
