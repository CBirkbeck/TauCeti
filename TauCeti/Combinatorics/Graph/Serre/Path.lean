/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic

/-!
# Paths without immediate reversal in a Serre graph

A path in the quiver of a Serre graph is reduced when no consecutive darts cancel. This
condition retains the distinction between a loop and its reversed dart, and between parallel
edges. It is the local normal-form condition used for graph path groups and Stallings graphs.
-/

public section

namespace SerreGraph

variable (Γ : SerreGraph)

local instance : Quiver Γ.V := Γ.toQuiver

/-- A Serre path has no consecutive pair of mutually reversed darts. -/
def Path.IsReduced {a : Γ.V} : ∀ {b : Γ.V}, Γ.Path a b → Prop
  | _, .nil => True
  | _, .cons .nil _ => True
  | _, .cons (.cons p e) f =>
      Path.IsReduced (.cons p e) ∧ f.1 ≠ Γ.rev e.1

@[simp] theorem Path.isReduced_nil (a : Γ.V) :
    Path.IsReduced Γ (Quiver.Path.nil : Γ.Path a a) := trivial

@[simp] theorem Path.isReduced_singleton {a b : Γ.V} (e : @Quiver.Hom Γ.V Γ.toQuiver a b) :
    Path.IsReduced Γ (Quiver.Path.nil.cons e) := trivial

/-- The reducedness test for a newly appended dart only examines the preceding dart. -/
@[simp] theorem Path.isReduced_cons_cons {a b c d : Γ.V}
    (p : Γ.Path a b) (e : @Quiver.Hom Γ.V Γ.toQuiver b c)
    (f : @Quiver.Hom Γ.V Γ.toQuiver c d) :
    Path.IsReduced Γ ((p.cons e).cons f) ↔
      Path.IsReduced Γ (p.cons e) ∧ f.1 ≠ Γ.rev e.1 := Iff.rfl

/-- Traversing a rose petal and then its reverse is a backtrack. -/
theorem rose_not_isReduced_backtrack {α : Type*} (a : α) :
    ¬ Path.IsReduced (rose α)
      ((Quiver.Path.nil.cons ((rose α).dart (a, true))).cons
        ((rose α).dart (a, false))) := by
  simp [Path.IsReduced, rose]

/-- Traversing one rose petal and then the reverse of a different petal is reduced. -/
theorem rose_isReduced_distinct_petals {α : Type*} {a b : α} (hab : a ≠ b) :
    Path.IsReduced (rose α)
      ((Quiver.Path.nil.cons ((rose α).dart (a, true))).cons
        ((rose α).dart (b, false))) := by
  simpa [Path.IsReduced, rose] using hab.symm

end SerreGraph
