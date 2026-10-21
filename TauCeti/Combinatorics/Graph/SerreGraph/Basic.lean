/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.List.Chain

/-!
# Graphs with edge reversal

A Serre graph has directed edges paired by a fixed-point-free reversal. In particular, a loop
has two distinct orientations, and parallel edges remain distinct. `Path` records a list of
incident darts, `Path.IsReduced` excludes immediate reversal, and `Reachable` and `Connected`
describe path connectivity. `IsTree` excludes nonempty reduced closed paths. The point graph
and roses give basic examples. This is the combinatorial carrier for labelled subgroup graphs
and graphs of groups.

The definition follows Serre, *Trees*, Chapter I, §2.1.
-/

public section

namespace TauCeti

/-- A graph in the sense of Serre, with a fixed-point-free reversal of its directed edges. -/
structure SerreGraph where
  /-- Vertices. -/
  V : Type*
  /-- Directed edges, also called darts. -/
  E : Type*
  /-- Origin of a directed edge. -/
  src : E → V
  /-- Reversal of a directed edge. -/
  rev : E → E
  /-- Reversing twice fixes every edge. -/
  rev_rev : ∀ e, rev (rev e) = e
  /-- An edge is distinct from its reversal, even when it is a loop. -/
  rev_ne : ∀ e, rev e ≠ e

attribute [simp] SerreGraph.rev_rev

namespace SerreGraph

variable (Γ : SerreGraph)

/-- The terminus of an edge is the origin of its reverse. -/
@[expose] def tgt (e : Γ.E) : Γ.V := Γ.src (Γ.rev e)

/-- The target of a dart is the source of its reverse. -/
theorem tgt_def (e : Γ.E) : Γ.tgt e = Γ.src (Γ.rev e) := rfl

/-- The reverse dart starts at the original target. -/
@[simp] theorem src_rev (e : Γ.E) : Γ.src (Γ.rev e) = Γ.tgt e := rfl

/-- Reversing darts is an involution. -/
theorem rev_involutive : Function.Involutive Γ.rev := Γ.rev_rev

/-- Reversing darts is injective. -/
theorem rev_injective : Function.Injective Γ.rev := Γ.rev_involutive.injective

@[simp] theorem tgt_rev (e : Γ.E) : Γ.tgt (Γ.rev e) = Γ.src e := by
  simp only [tgt, Γ.rev_rev]

/-- A list of darts is a path from `u` to `v` when it can be traversed from `u` and ends at
`v`. The empty list is a path precisely when its endpoints agree. -/
@[expose] def Valid (Γ : SerreGraph) : Γ.V → List Γ.E → Γ.V → Prop
  | u, [], v => u = v
  | u, e :: es, v => Γ.src e = u ∧ Γ.Valid (Γ.tgt e) es v

@[simp] theorem valid_nil (u v : Γ.V) : Γ.Valid u [] v ↔ u = v := Iff.rfl

@[simp] theorem valid_cons (u v : Γ.V) (e : Γ.E) (es : List Γ.E) :
    Γ.Valid u (e :: es) v ↔ Γ.src e = u ∧ Γ.Valid (Γ.tgt e) es v := Iff.rfl

/-- A directed edge path with specified endpoints. -/
structure Path (u v : Γ.V) where
  /-- The traversed darts. -/
  edges : List Γ.E
  /-- Incidence and endpoint conditions. -/
  valid : Γ.Valid u edges v

namespace Path

variable {Γ} {u v w : Γ.V}

@[ext] theorem ext {p q : Γ.Path u v} (h : p.edges = q.edges) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- The empty path at a vertex. -/
@[expose] def nil (u : Γ.V) : Γ.Path u u := ⟨[], rfl⟩

@[simp] theorem nil_edges (u : Γ.V) : (nil u).edges = [] := rfl

/-- Prefix a path by a dart ending at its initial vertex. -/
@[expose] def cons (e : Γ.E) (p : Γ.Path (Γ.tgt e) v) : Γ.Path (Γ.src e) v :=
  ⟨e :: p.edges, ⟨rfl, p.valid⟩⟩

@[simp] theorem cons_edges (e : Γ.E) (p : Γ.Path (Γ.tgt e) v) :
    (cons e p).edges = e :: p.edges := rfl

/-- The edge list of a concatenation satisfies the path incidence conditions. -/
theorem valid_append (p : Γ.Path u v) (q : Γ.Path v w) :
    Γ.Valid u (p.edges ++ q.edges) w := by
  obtain ⟨es, hes⟩ := p
  induction es generalizing u with
  | nil =>
      simp only [List.nil_append] at *
      subst u
      exact q.valid
  | cons e es ih =>
      simp only [valid_cons] at hes ⊢
      exact ⟨hes.1, ih hes.2⟩

/-- Concatenation of directed paths. -/
@[expose] def append (p : Γ.Path u v) (q : Γ.Path v w) : Γ.Path u w :=
  ⟨p.edges ++ q.edges, valid_append p q⟩

@[simp] theorem append_edges (p : Γ.Path u v) (q : Γ.Path v w) :
    (append p q).edges = p.edges ++ q.edges := rfl

@[simp] theorem nil_append (p : Γ.Path u v) : append (nil u) p = p := by
  ext
  simp

@[simp] theorem append_nil (p : Γ.Path u v) : append p (nil v) = p := by
  ext
  simp

/-- Path concatenation is associative. -/
@[simp]
theorem append_assoc (p : Γ.Path u v) (q : Γ.Path v w) {z : Γ.V}
    (r : Γ.Path w z) : append (append p q) r = append p (append q r) := by
  ext
  simp [List.append_assoc]

/-- Prefixing a concatenation is the same as prefixing its first path. -/
@[simp] theorem cons_append (e : Γ.E) (p : Γ.Path (Γ.tgt e) v)
    (q : Γ.Path v w) : (cons e p).append q = cons e (p.append q) := by
  ext
  simp

/-- Reversing and flipping every dart preserves the path incidence conditions. -/
theorem valid_reverse {es : List Γ.E} (h : Γ.Valid u es v) :
    Γ.Valid v (es.reverse.map Γ.rev) u := by
  induction es generalizing u with
  | nil =>
      simp only [valid_nil] at h ⊢
      exact h.symm
  | cons e es ih =>
      obtain ⟨rfl, ht⟩ := (Γ.valid_cons u v e es).mp h
      simp only [List.reverse_cons, List.map_append, List.map_singleton]
      have hstep : Γ.Valid (Γ.tgt e) [Γ.rev e] (Γ.src e) := by
        simp only [valid_cons, valid_nil, src_rev, tgt_rev, true_and]
      exact valid_append ⟨_, ih ht⟩ ⟨_, hstep⟩

/-- Reverse a path, reversing both the order and the orientation of its darts. -/
@[expose] def reverse (p : Γ.Path u v) : Γ.Path v u :=
  ⟨p.edges.reverse.map Γ.rev, valid_reverse p.valid⟩

@[simp] theorem reverse_edges (p : Γ.Path u v) :
    p.reverse.edges = p.edges.reverse.map Γ.rev := rfl

/-- Reversing a path twice returns the original path. -/
@[simp] theorem reverse_reverse (p : Γ.Path u v) : p.reverse.reverse = p := by
  ext
  simp [List.map_map, Γ.rev_rev]

@[simp] theorem reverse_nil (u : Γ.V) : (nil u).reverse = nil u := by
  ext
  rfl

/-- Reversing a prefixed path moves its dart to the end with opposite orientation. -/
theorem reverse_cons (e : Γ.E) (p : Γ.Path (Γ.tgt e) v) :
    (cons e p).reverse.edges = p.reverse.edges ++ [Γ.rev e] := by
  simp [List.reverse_cons, List.map_append]

/-- Reversal exchanges the order of concatenated paths. -/
theorem reverse_append (p : Γ.Path u v) (q : Γ.Path v w) :
    (append p q).reverse = append q.reverse p.reverse := by
  ext
  simp [List.reverse_append, List.map_append]

/-- A path is reduced when no dart is immediately followed by its reverse. -/
def IsReduced (p : Γ.Path u v) : Prop :=
  p.edges.IsChain fun e f => f ≠ Γ.rev e

/-- A prefixed path is reduced exactly when its tail is reduced and its first dart does not
reverse the new prefix. -/
theorem isReduced_cons (e : Γ.E) (p : Γ.Path (Γ.tgt e) v) :
    IsReduced (cons e p) ↔ p.IsReduced ∧ ∀ f ∈ p.edges.head?, f ≠ Γ.rev e := by
  simp only [IsReduced, cons_edges, List.isChain_cons, and_comm]

/-- Reversing a path preserves and reflects reducedness. -/
@[simp] theorem isReduced_reverse (p : Γ.Path u v) :
    p.reverse.IsReduced ↔ p.IsReduced := by
  simp only [IsReduced, reverse_edges, List.isChain_map, List.isChain_reverse]
  apply List.IsChain.iff
  intro e f
  simp only [Γ.rev_rev]
  exact ne_comm

@[simp] theorem isReduced_nil (u : Γ.V) : IsReduced (nil u) := by
  simp [IsReduced]

@[simp] theorem isReduced_single (e : Γ.E) :
    IsReduced (cons e (nil (Γ.tgt e))) := by
  simp [IsReduced]

end Path

/-- Two vertices are path-connected when a directed path joins them. -/
def Reachable (u v : Γ.V) : Prop := Nonempty (Γ.Path u v)

namespace Reachable

/-- Every vertex is reachable from itself. -/
@[refl] theorem refl (u : Γ.V) : Γ.Reachable u u := ⟨Path.nil u⟩

/-- Reversing a path reverses reachability. -/
@[symm] theorem symm {u v : Γ.V} (h : Γ.Reachable u v) : Γ.Reachable v u :=
  h.elim fun p => ⟨p.reverse⟩

/-- Composing paths composes reachability. -/
@[trans] theorem trans {u v w : Γ.V} (huv : Γ.Reachable u v)
    (hvw : Γ.Reachable v w) : Γ.Reachable u w :=
  huv.elim fun p => hvw.elim fun q => ⟨p.append q⟩

end Reachable

/-- Path reachability is an equivalence relation on vertices. -/
theorem reachable_equivalence : Equivalence Γ.Reachable :=
  ⟨Reachable.refl Γ, Reachable.symm Γ, Reachable.trans Γ⟩

/-- The setoid whose classes are the path components. -/
def reachableSetoid : Setoid Γ.V := Setoid.mk Γ.Reachable Γ.reachable_equivalence

/-- Every pair of vertices is joined by a path. This holds vacuously for the empty graph. -/
def Preconnected : Prop := ∀ u v : Γ.V, Γ.Reachable u v

/-- A Serre graph is connected when it has a vertex and any two vertices are joined. -/
def Connected : Prop := Nonempty Γ.V ∧ Γ.Preconnected

theorem connected_iff : Γ.Connected ↔ Nonempty Γ.V ∧ ∀ u v : Γ.V, Γ.Reachable u v :=
  Iff.rfl

/-- A tree is a nonempty connected Serre graph with no nonempty reduced closed path. -/
def IsTree : Prop :=
  Γ.Connected ∧ ∀ (u : Γ.V) (p : Γ.Path u u), p.IsReduced → p.edges = []

namespace IsTree

/-- Every tree is connected. -/
theorem connected (h : Γ.IsTree) : Γ.Connected := h.1

/-- Every reduced closed path in a tree is empty. -/
theorem edges_eq_nil_of_isReduced (h : Γ.IsTree) {u : Γ.V} (p : Γ.Path u u)
    (hp : p.IsReduced) : p.edges = [] := h.2 u p hp

end IsTree

/-- Characterization of a Serre tree by connectedness and reduced closed paths. -/
theorem isTree_iff : Γ.IsTree ↔
    Γ.Connected ∧ ∀ (u : Γ.V) (p : Γ.Path u u), p.IsReduced → p.edges = [] := Iff.rfl

/-- The Serre graph with one vertex and no edges. -/
abbrev point : SerreGraph where
  V := PUnit
  E := PEmpty
  src := PEmpty.elim
  rev := PEmpty.elim
  rev_rev := by intro e; exact e.elim
  rev_ne := by intro e; exact e.elim

/-- The graph with one vertex and no edges is a tree. -/
theorem point_isTree : point.IsTree := by
  refine ⟨⟨⟨PUnit.unit⟩, ?_⟩, ?_⟩
  · intro u v
    cases u
    cases v
    exact Reachable.refl _ _
  · intro u p _
    cases p with
    | mk es _ =>
      cases es with
      | nil => rfl
      | cons e _ => exact PEmpty.elim e

/-- The rose with petals indexed by `α`. Each petal has two distinct orientations. -/
@[expose] def rose (α : Type*) : SerreGraph where
  V := PUnit
  E := α × Bool
  src := fun _ => PUnit.unit
  rev := fun e => (e.1, !e.2)
  rev_rev := by
    intro e
    cases e with
    | mk a b => cases b <;> rfl
  rev_ne := by
    intro e
    cases e with
    | mk a b => cases b <;> simp

/-- Every rose is connected, including the rose with no petals. -/
theorem rose_connected (α : Type*) : (rose α).Connected := by
  refine ⟨⟨PUnit.unit⟩, ?_⟩
  intro u v
  cases u
  cases v
  exact Reachable.refl _ _

/-- A petal is a nonempty reduced loop in the rose. -/
@[expose] def rosePetal {α : Type*} (a : α) : (rose α).Path PUnit.unit PUnit.unit :=
  Path.cons (a, true) (Path.nil ((rose α).tgt (a, true)))

@[simp] theorem rosePetal_edges {α : Type*} (a : α) :
    (rosePetal a).edges = [(a, true)] := rfl

theorem rosePetal_isReduced {α : Type*} (a : α) :
    (rosePetal a).IsReduced := Path.isReduced_single _

/-- A rose with a petal is not a tree: the petal gives a nonempty reduced loop. -/
theorem rose_not_isTree {α : Type*} (a : α) : ¬(rose α).IsTree := by
  intro ht
  have h := ht.2 PUnit.unit (rosePetal a) (rosePetal_isReduced a)
  simp at h

end SerreGraph
end TauCeti
