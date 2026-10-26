/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path
public import TauCeti.Combinatorics.Graph.Connectivity.Component

/-!
# The multigraph underlying a Serre graph

Reversal pairs of darts are the edges of the underlying undirected multigraph. This
construction retains loops and parallel edges, while its walks forget which direction of a
loop was chosen. Path reachability and connectedness agree with those of the multigraph.

The directed paths remain necessary for the fundamental group of a graph: the two darts of a
loop represent inverse generators, even though they give the same one-edge undirected walk.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.1–2.2.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- Two darts represent the same undirected edge when they are equal or reverse one another. -/
@[expose] def edgeSetoid : Setoid Γ.E where
  r e f := e = f ∨ e = Γ.rev f
  iseqv := ⟨fun _ => Or.inl rfl,
    by
      intro e f h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by rw [h, Γ.rev_rev]),
    by
      intro e f g h k
      rcases h with rfl | h
      · exact k
      · rcases k with rfl | k
        · exact Or.inr h
        · exact Or.inl (by rw [h, k, Γ.rev_rev])⟩

/-- The undirected edge carried by a dart, identified with its reverse. -/
abbrev Edge : Type _ := Quotient Γ.edgeSetoid

/-- The reversal orbit of a dart. -/
@[expose] def edge (e : Γ.E) : Γ.Edge := Quotient.mk Γ.edgeSetoid e

@[simp] theorem edge_rev (e : Γ.E) : Γ.edge (Γ.rev e) = Γ.edge e :=
  Quotient.sound (Or.inr rfl)

/-- Two darts determine the same edge exactly when they agree up to reversal. -/
theorem edge_eq_iff (e f : Γ.E) :
    Γ.edge e = Γ.edge f ↔ e = f ∨ e = Γ.rev f := Quotient.eq

/-- The ends of a reversal orbit, as an unordered pair. -/
@[expose] def edgeEnds (q : Γ.Edge) : Sym2 Γ.V :=
  Quotient.liftOn q (fun e => s(Γ.src e, Γ.tgt e)) (by
    intro e f h
    rcases h with rfl | h
    · rfl
    · subst e
      simp only [Γ.src_rev, Γ.tgt_rev]
      exact Sym2.eq_swap)

@[simp] theorem edgeEnds_edge (e : Γ.E) :
    Γ.edgeEnds (Γ.edge e) = s(Γ.src e, Γ.tgt e) := rfl

/-- The undirected multigraph whose edges are reversal pairs of darts. -/
@[expose] def toGraph : Graph Γ.V Γ.Edge where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink q x y := Γ.edgeEnds q = s(x, y)
  isLink_symm := by
    aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by
    intro q x y v w h k
    have h' : s(x, y) = s(v, w) := h.symm.trans k
    rcases Sym2.eq_iff.mp h' with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  edge_mem_iff_exists_isLink := by
    intro q
    constructor
    · intro _
      induction q using Quotient.inductionOn with
      | _ e => exact ⟨Γ.src e, Γ.tgt e, rfl⟩
    · intro _
      trivial
  left_mem_of_isLink := by
    intro q x y h
    trivial

@[simp] theorem vertexSet_toGraph : (Γ.toGraph).vertexSet = Set.univ := rfl

@[simp] theorem edgeSet_toGraph : (Γ.toGraph).edgeSet = Set.univ := rfl

@[simp] theorem toGraph_isLink (q : Γ.Edge) (x y : Γ.V) :
    Γ.toGraph.IsLink q x y ↔ Γ.edgeEnds q = s(x, y) := Iff.rfl

/-- A Serre dart links its endpoints in the underlying multigraph. -/
theorem toGraph_isLink_edge {u v : Γ.V} (e : Quiver.Hom u v) :
    Γ.toGraph.IsLink (Γ.edge e.1) u v := by
  rw [toGraph_isLink, edgeEnds_edge]
  exact congrArg₂ (fun x y => s(x, y)) e.2.1 e.2.2

/-- Forget the directions of a Serre path, retaining its edge orbits. -/
@[expose] def Path.toWalk {u v : Γ.V} (p : Γ.Path u v) : Γ.toGraph.Walk u v := by
  induction p with
  | nil => exact .nil
  | @cons a b p e ih =>
    exact ih.append (Γ.toGraph_isLink_edge e).toWalk

@[simp] theorem Path.toWalk_nil (u : Γ.V) :
    Path.toWalk Γ (Quiver.Path.nil : Γ.Path u u) = .nil := rfl

@[simp] theorem Path.toWalk_cons {u v w : Γ.V} (p : Γ.Path u v)
    (e : Quiver.Hom v w) :
    Path.toWalk Γ (p.cons e) = (Path.toWalk Γ p).append
      (Γ.toGraph_isLink_edge e).toWalk := rfl

@[simp] theorem Path.toWalk_comp {u v w : Γ.V} (p : Γ.Path u v)
    (q : Γ.Path v w) :
    Path.toWalk Γ (p.comp q) = (Path.toWalk Γ p).append (Path.toWalk Γ q) := by
  induction q with
  | nil => simp
  | cons q e ih =>
    simp only [Quiver.Path.comp_cons, Path.toWalk_cons, ih, Graph.Walk.append_assoc]

@[simp] theorem Path.toWalk_dart {u v : Γ.V} (e : Quiver.Hom u v) :
    Path.toWalk Γ e.toPath = (Γ.toGraph_isLink_edge e).toWalk := by
  simp [Quiver.Hom.toPath]

/-- Every walk between vertices lifts to a directed Serre path. A loop walk generally has
more than one lift. -/
theorem exists_path_toWalk {u v : Γ.V} (p : Γ.toGraph.Walk u v) :
    ∃ q : Γ.Path u v, q.toWalk = p := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons u v w e h p ih =>
    induction e using Quotient.inductionOn with
    | _ d =>
      rw [toGraph_isLink] at h
      -- The quotient representative must be exposed before rewriting its endpoints.
      change Γ.edgeEnds (Γ.edge d) = s(u, v) at h
      rw [edgeEnds_edge, Sym2.eq_iff] at h
      rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · subst u
        subst v
        rcases ih with ⟨q, rfl⟩
        refine ⟨(Γ.dart d).toPath.comp q, ?_⟩
        simp [Graph.IsLink.toWalk_eq_cons, edge]
      · subst u
        subst v
        rcases ih with ⟨q, rfl⟩
        let step : Quiver.Hom (Γ.tgt d) (Γ.src d) :=
          ⟨Γ.rev d, by simp⟩
        refine ⟨step.toPath.comp q, ?_⟩
        simp only [Path.toWalk_comp, Path.toWalk_dart, Graph.IsLink.toWalk_eq_cons,
          Graph.Walk.cons_append,
          Graph.Walk.nil_append]
        simp only [Graph.Walk.cons.injEq, heq_eq_eq, and_true, true_and]
        exact Γ.edge_rev d

/-- Serre path reachability agrees with reachability in the underlying multigraph. -/
theorem reachable_toGraph (u v : Γ.V) :
    Nonempty (Γ.Path u v) ↔ Γ.toGraph.Reachable u v := by
  rw [Graph.reachable_def]
  simp only [vertexSet_toGraph, Set.mem_univ, true_and]
  constructor
  · rintro ⟨p⟩
    exact ⟨p.toWalk⟩
  · rintro ⟨p⟩
    exact ⟨(Γ.exists_path_toWalk p).choose⟩

/-- A Serre graph is preconnected when any two vertices are joined by a path. -/
def Preconnected : Prop := ∀ u v : Γ.V, Nonempty (Γ.Path u v)

/-- A Serre graph is connected when it is nonempty and path-connected. -/
def Connected : Prop := Nonempty Γ.V ∧ Γ.Preconnected

/-- Connectedness agrees with that of the underlying multigraph, including the empty graph. -/
theorem connected_toGraph : Γ.toGraph.Connected ↔ Γ.Connected := by
  rw [Graph.connected_iff_forall_reachable]
  simp only [vertexSet_toGraph, Set.mem_univ, true_implies]
  rw [Connected, Preconnected]
  constructor
  · intro h
    rcases h with ⟨⟨u, _⟩, hreach⟩
    exact ⟨⟨u⟩, fun x y => (Γ.reachable_toGraph x y).mpr
      (hreach (x := x) (y := y))⟩
  · intro h
    rcases h with ⟨⟨u⟩, hpath⟩
    exact ⟨⟨u, trivial⟩, fun x y => (Γ.reachable_toGraph x y).mp (hpath x y)⟩

/-- Two vertices lie in the same underlying multigraph component exactly when a Serre path
joins them. This also covers loops, parallel edges, and isolated vertices. -/
theorem connectedComponentOf_eq_iff (u v : Γ.V) :
    Γ.toGraph.connectedComponentOf u (by simp) =
      Γ.toGraph.connectedComponentOf v (by simp) ↔ Nonempty (Γ.Path u v) := by
  rw [Graph.connectedComponentOf_eq_connectedComponentOf_iff]
  exact (Γ.reachable_toGraph u v).symm

end SerreGraph
end TauCeti
