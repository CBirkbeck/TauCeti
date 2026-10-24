/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Algebra.Group.End

/-!
# Subgroups read by labelled graphs

A labelled Serre graph assigns inverse letters to reversed darts. Reading the labels of
closed paths at a vertex gives a subgroup of the free group. Morphisms of based labelled
graphs preserve this subgroup. The base vertex matters: moving it along a path conjugates
the accepted subgroup.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*, Sections 2–3.
-/

public section

namespace TauCeti

universe u v w

/-- A Serre graph whose reversed darts have inverse free-group labels. -/
structure StallingsGraph (α : Type u) where
  /-- The underlying graph. -/
  graph : SerreGraph.{v, w}
  /-- The distinguished vertex. -/
  base : graph.V
  /-- The letter read along each dart. -/
  label : graph.E → α × Bool
  /-- Reversing a dart inverts its label. -/
  label_rev : ∀ e, label (graph.rev e) = ((label e).1, !(label e).2)

namespace StallingsGraph

variable {α : Type*} (S : StallingsGraph α)

/-- The label word of a path, in traversal order. -/
def word {a : S.graph.V} : ∀ {b : S.graph.V}, S.graph.Path a b → List (α × Bool)
  | _, .nil => []
  | _, .cons p e => word p ++ [S.label e.1]

@[simp] theorem word_nil (a : S.graph.V) :
    S.word (Quiver.Path.nil : S.graph.Path a a) = [] := by simp [word]

@[simp] theorem word_cons {a b c : S.graph.V} (p : S.graph.Path a b)
    (e : Quiver.Hom b c) : S.word (p.cons e) = S.word p ++ [S.label e.1] := by
  simp [word]

@[simp] theorem word_toPath {a b : S.graph.V} (e : Quiver.Hom a b) :
    S.word e.toPath = [S.label e.1] := by simp [Quiver.Hom.toPath]

@[simp] theorem word_comp {a b c : S.graph.V} (p : S.graph.Path a b)
    (q : S.graph.Path b c) : S.word (p.comp q) = S.word p ++ S.word q := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, List.append_assoc]

/-- The free-group element represented by the word of a path. -/
def read {a b : S.graph.V} (p : S.graph.Path a b) : FreeGroup α :=
  FreeGroup.mk (S.word p)

@[simp] theorem read_nil (a : S.graph.V) :
    S.read (Quiver.Path.nil : S.graph.Path a a) = 1 := by
  simp [read, FreeGroup.one_eq_mk]

@[simp] theorem read_comp {a b c : S.graph.V} (p : S.graph.Path a b)
    (q : S.graph.Path b c) : S.read (p.comp q) = S.read p * S.read q := by
  simp [read, FreeGroup.mul_mk]

@[simp] theorem word_reverse {a b : S.graph.V} (p : S.graph.Path a b) :
    S.word p.reverse = FreeGroup.invRev (S.word p) := by
  induction p with
  | nil => simp [FreeGroup.invRev]
  | cons p e ih =>
    simp [Quiver.Path.reverse, ih, FreeGroup.invRev, S.label_rev]

@[simp] theorem read_reverse {a b : S.graph.V} (p : S.graph.Path a b) :
    S.read p.reverse = (S.read p)⁻¹ := by
  simp [read, FreeGroup.inv_mk]

/-- The subgroup of the free group read by closed paths at a vertex. -/
def subgroup (a : S.graph.V) : Subgroup (FreeGroup α) where
  carrier := {g | ∃ p : S.graph.Path a a, S.read p = g}
  one_mem' := ⟨.nil, S.read_nil a⟩
  mul_mem' := by
    rintro x y ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p.comp q, S.read_comp p q⟩
  inv_mem' := by
    rintro x ⟨p, rfl⟩
    exact ⟨p.reverse, S.read_reverse p⟩

theorem mem_subgroup_iff {a : S.graph.V} {g : FreeGroup α} :
    g ∈ S.subgroup a ↔ ∃ p : S.graph.Path a a, S.read p = g := Iff.rfl

theorem read_mem_subgroup {a : S.graph.V} (p : S.graph.Path a a) :
    S.read p ∈ S.subgroup a := ⟨p, rfl⟩

/-- Moving the base vertex along a path conjugates the accepted subgroup by its label. -/
theorem subgroup_conj {a b : S.graph.V} (p : S.graph.Path a b) :
    S.subgroup b = (S.subgroup a).map (MulAut.conj (S.read p)⁻¹).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv]
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨(p.comp q).comp p.reverse, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨q, hq⟩
    refine ⟨(p.reverse.comp q).comp p, ?_⟩
    simp only [read_comp, read_reverse]
    rw [MulAut.conj_symm_apply] at hq
    simp only [inv_inv] at hq
    calc
      (S.read p)⁻¹ * S.read q * S.read p =
          (S.read p)⁻¹ * (S.read p * g * (S.read p)⁻¹) * S.read p := by rw [hq]
      _ = g := by simp [mul_assoc]

/-- A map of labelled graphs preserves the underlying darts and their labels. -/
structure Hom (T : StallingsGraph α) where
  /-- The map of underlying Serre graphs. -/
  graphHom : S.graph.Hom T.graph
  /-- The distinguished vertex is preserved. -/
  map_base : graphHom.mapV S.base = T.base
  /-- Labels are preserved. -/
  label_map : ∀ e, T.label (graphHom.mapE e) = S.label e

namespace Hom

variable {S} {T : StallingsGraph α} (f : S.Hom T)

@[simp] theorem word_mapPath {a b : S.graph.V} (p : S.graph.Path a b) :
    T.word (f.graphHom.mapPath p) = S.word p := by
  induction p with
  | nil => simp
  | cons p e ih => simp only [SerreGraph.Hom.mapPath_cons, word_cons, ih,
      f.label_map]

@[simp] theorem read_mapPath {a b : S.graph.V} (p : S.graph.Path a b) :
    T.read (f.graphHom.mapPath p) = S.read p := by simp [StallingsGraph.read]

/-- A based label-preserving morphism sends every accepted word to an accepted word. -/
theorem subgroup_le (f : S.Hom T) : S.subgroup S.base ≤ T.subgroup T.base := by
  rintro g ⟨p, rfl⟩
  rw [← f.map_base]
  exact ⟨f.graphHom.mapPath p, f.read_mapPath p⟩

end Hom

/-- The rose with one petal for each generator, labelled by those generators. -/
@[expose] def rose (α : Type*) : StallingsGraph α where
  graph := SerreGraph.rose α
  base := PUnit.unit
  label := id
  label_rev := by intro ⟨a, b⟩; rfl

/-- Every free-group element is read by a loop in the rose. -/
theorem rose_subgroup_top (α : Type*) :
    (rose α).subgroup PUnit.unit = ⊤ := by
  apply top_unique
  intro g _
  have all : ∀ h : FreeGroup α, h ∈ (rose α).subgroup PUnit.unit := by
    intro h
    induction h using FreeGroup.induction_on with
    | one => exact Subgroup.one_mem _
    | of x =>
      exact ⟨((rose α).graph.dart (x, true)).toPath, by
        simp only [rose, read, word, Quiver.Hom.toPath, FreeGroup.of,
          List.nil_append, id_eq]
        congr 1
        congr 1
        exact (SerreGraph.dart_val (SerreGraph.rose α) (x, true))⟩
    | inv_of x hx => exact Subgroup.inv_mem _ hx
    | mul x y hx hy => exact Subgroup.mul_mem _ hx hy
  exact all g

end StallingsGraph

end TauCeti
