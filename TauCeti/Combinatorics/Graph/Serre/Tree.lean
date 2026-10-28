/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path

/-!
# Trees of Serre graphs

A Serre tree is a nonempty connected graph without a nonempty reduced closed path. The
one-vertex graph without edges is a tree. A rose with a petal is not a tree, since its petal
is a reduced loop.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- A tree is a connected Serre graph in which every reduced closed path is empty. -/
def IsTree : Prop :=
  Γ.Connected ∧ ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p → p = Quiver.Path.nil

namespace IsTree

/-- Every tree is connected. -/
theorem connected (h : Γ.IsTree) : Γ.Connected := h.1

/-- Every reduced closed path in a tree is empty. -/
theorem eq_nil_of_isReduced (h : Γ.IsTree) {u : Γ.V} (p : Γ.Path u u)
    (hp : Path.IsReduced Γ p) : p = Quiver.Path.nil := h.2 u p hp

end IsTree

/-- Characterization of Serre trees by connectedness and reduced closed paths. -/
theorem isTree_iff : Γ.IsTree ↔
    Γ.Connected ∧ ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p →
      p = Quiver.Path.nil := Iff.rfl

/-- The Serre graph with one vertex and no edges. -/
def point : SerreGraph where
  V := PUnit
  E := PEmpty
  src := PEmpty.elim
  rev := PEmpty.elim
  rev_rev := by intro e; exact e.elim
  rev_ne := by intro e; exact e.elim

/-- The graph with one vertex and no edges is a tree. -/
theorem single_vertex_isTree : point.IsTree := by
  change point.Connected ∧ ∀ (u : point.V) (p : point.Path u u),
    Path.IsReduced point p → p = Quiver.Path.nil
  refine ⟨?_, ?_⟩
  · rw [point.connected_iff]
    refine ⟨⟨PUnit.unit⟩, ?_⟩
    rw [point.preconnected_iff]
    intro u v
    cases u
    cases v
    exact ⟨Quiver.Path.nil⟩
  · intro u p _
    cases p with
    | nil => rfl
    | cons p e => exact e.1.elim

/-- Every rose is connected, including the rose without petals. -/
theorem rose_connected (α : Type*) : (rose α).Connected := by
  rw [(rose α).connected_iff]
  refine ⟨⟨PUnit.unit⟩, ?_⟩
  rw [(rose α).preconnected_iff]
  intro u v
  cases u
  cases v
  exact ⟨Quiver.Path.nil⟩

/-- A rose petal is a closed path of length one. -/
def rosePetal {α : Type*} (a : α) : (rose α).Path PUnit.unit PUnit.unit :=
  ((rose α).dart (a, true)).toPath

/-- A rose petal is the path consisting of its positive dart. -/
theorem rosePetal_eq_toPath {α : Type*} (a : α) :
    rosePetal a = ((rose α).dart (a, true)).toPath := (rfl)

@[simp] theorem rosePetal_length {α : Type*} (a : α) :
    (rosePetal a).length = 1 := by
  rw [rosePetal_eq_toPath]
  exact Quiver.Path.length_toPath _

/-- A rose petal is reduced. -/
theorem rosePetal_isReduced {α : Type*} (a : α) :
    Path.IsReduced (rose α) (rosePetal a) := by
  exact Path.isReduced_toPath _ _

/-- A rose with a petal is not a tree. -/
theorem rose_not_isTree {α : Type*} (a : α) : ¬(rose α).IsTree := by
  intro h
  have hp := h.eq_nil_of_isReduced (rose α) (rosePetal a) (rosePetal_isReduced a)
  cases hp

/-- The one-petal rose is not a tree. -/
theorem rose_one_not_tree : ¬(rose PUnit).IsTree :=
  rose_not_isTree PUnit.unit

end SerreGraph
end TauCeti
