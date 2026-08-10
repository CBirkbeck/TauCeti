/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# A first-countable nonarchimedean group has a decreasing basis of open subgroups

Henkel's open mapping theorem runs a successive-approximation argument down a *sequence* of
neighbourhoods of zero, each one absorbing the previous error. Two properties of that sequence are
used and neither comes for free: its terms must be **subgroups**, so that a sum of errors drawn
from one term stays inside it, and it must be **decreasing**, so that the tail of the construction
stays inside the neighbourhood it started in.

Nonarchimedean gives the first, first countability the second, and this file combines them:
`TauCeti.exists_antitone_basis_openAddSubgroup`. Neither hypothesis alone suffices — a
nonarchimedean group has open subgroups arbitrarily close to zero but possibly uncountably many
with no cofinal sequence among them, and a first-countable group has a decreasing countable basis
whose terms need not be subgroups.

## Main results

* `TauCeti.exists_antitone_basis_openAddSubgroup`: the neighbourhoods of zero admit an antitone
  basis consisting of open subgroups, indexed by `ℕ`.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647), whose approximation argument needs such a
  sequence.
-/

public section

open Filter Topology

namespace TauCeti

variable {G : Type*} [AddGroup G] [TopologicalSpace G]

/-- **A first-countable nonarchimedean additive group has an antitone basis of open subgroups at
zero.**

Both hypotheses are used. Nonarchimedean supplies an open *subgroup* inside each member of some
countable basis; first countability supplies the countable basis, and lets the subgroups be
intersected downwards into an antitone sequence — a finite intersection of open subgroups is again
one, so nothing is lost. -/
theorem exists_antitone_basis_openAddSubgroup [FirstCountableTopology G]
    [NonarchimedeanAddGroup G] :
    ∃ V : ℕ → OpenAddSubgroup G, (𝓝 (0 : G)).HasAntitoneBasis fun n ↦ (V n : Set G) := by
  obtain ⟨U, hU⟩ := (𝓝 (0 : G)).exists_antitone_basis
  -- An open subgroup inside each basic neighbourhood.
  choose W hW using fun n ↦ NonarchimedeanAddGroup.is_nonarchimedean (U n)
    (hU.toHasBasis.mem_of_mem (i := n) trivial)
  -- Intersecting the first `n + 1` of them makes the sequence antitone without leaving `U n`.
  set V : ℕ → OpenAddSubgroup G := fun n ↦ Nat.rec (W 0) (fun m Vm ↦ Vm ⊓ W (m + 1)) n
  have hstep : ∀ n, V (n + 1) ≤ V n := fun n ↦ inf_le_left
  have hanti : Antitone fun n ↦ (V n : Set G) :=
    antitone_nat_of_succ_le fun n ↦ hstep n
  have hVW : ∀ n, (V n : Set G) ⊆ (W n : Set G) := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ m => exact inf_le_right
  refine ⟨V, ⟨?_, hanti⟩⟩
  refine Filter.hasBasis_iff.mpr fun S ↦ ⟨fun hS ↦ ?_, ?_⟩
  · obtain ⟨n, -, hn⟩ := hU.toHasBasis.mem_iff.mp hS
    exact ⟨n, trivial, ((hVW n).trans (hW n)).trans hn⟩
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset ((V n).isOpen.mem_nhds (V n).zero_mem) hn

end TauCeti

end
