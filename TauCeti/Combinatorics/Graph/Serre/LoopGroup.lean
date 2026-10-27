/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Reduction

/-!
# The reduced loop group of a Serre graph

Reduced closed paths at a vertex form a group: multiplication concatenates and reduces,
and inversion reverses the darts. Backtrack homotopy gives the equality criterion for
this group. The construction retains the two directions of a loop as inverse elements.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.2–2.3.
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph)

namespace Path

/-- Backtrack homotopy is preserved by appending a path. -/
theorem Homotopic.comp_right {a b c : Γ.V} {p q : Γ.Path a b}
    (h : Homotopic Γ p q) (r : Γ.Path b c) :
    Homotopic Γ (p.comp r) (q.comp r) := by
  induction r with
  | nil => simpa using h
  | cons r e ih => simpa only [Quiver.Path.comp_cons] using Homotopic.cons ih e

/-- Backtrack homotopy is preserved by prepending a path. -/
theorem Homotopic.comp_left {a b c : Γ.V} (p : Γ.Path a b) {q r : Γ.Path b c}
    (h : Homotopic Γ q r) : Homotopic Γ (p.comp q) (p.comp r) := by
  induction h with
  | refl q => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | cons h e ih => simpa only [Quiver.Path.comp_cons] using Homotopic.cons ih e
  | backtrack q e =>
      simpa only [Quiver.Path.comp_cons] using Homotopic.backtrack (p.comp q) e

/-- Reducing a prefix before concatenation does not change the reduced result. -/
theorem reduce_comp_reduce_left {a b c : Γ.V} (p : Γ.Path a b)
    (q : Γ.Path b c) :
    reduce Γ ((reduce Γ p).comp q) = reduce Γ (p.comp q) := by
  exact (Homotopic.comp_right Γ (homotopic_reduce Γ p) q).reduce_eq Γ |>.symm

/-- Reducing a suffix before concatenation does not change the reduced result. -/
theorem reduce_comp_reduce_right {a b c : Γ.V} (p : Γ.Path a b)
    (q : Γ.Path b c) :
    reduce Γ (p.comp (reduce Γ q)) = reduce Γ (p.comp q) := by
  exact (Homotopic.comp_left Γ p (homotopic_reduce Γ q)).reduce_eq Γ |>.symm

/-- A path followed by its reverse is backtrack homotopic to the empty path. -/
theorem homotopic_comp_reverse {a b : Γ.V} (p : Γ.Path a b) :
    Homotopic Γ (p.comp p.reverse) (Quiver.Path.nil : Γ.Path a a) := by
  induction p with
  | nil => simpa using (Homotopic.refl (Quiver.Path.nil : Γ.Path a a) : Homotopic Γ _ _)
  | cons p e ih =>
      rw [Quiver.Path.reverse, ← Quiver.Path.comp_assoc]
      have hback : Homotopic Γ ((p.cons e).comp (Quiver.reverse e).toPath) p := by
        simpa only [Quiver.Path.comp_cons, Quiver.Path.comp_nil,
          Quiver.Hom.toPath] using Homotopic.backtrack p e
      exact (hback.comp_right Γ p.reverse).trans ih

end Path

/-- Reduced closed paths at `v`; equality is literal equality of their normal forms. -/
@[expose] def ReducedLoop (v : Γ.V) :=
  {p : Γ.Path v v // Path.IsReduced Γ p}

namespace ReducedLoop

variable {Γ : SerreGraph} {v : Γ.V}

/-- A reduced path determines a reduced loop by normalisation. -/
@[expose] noncomputable def ofPath (p : Γ.Path v v) : ReducedLoop Γ v :=
  ⟨Path.reduce Γ p, Path.isReduced_reduce Γ p⟩

@[simp] theorem val_ofPath (p : Γ.Path v v) : (ofPath p).1 = Path.reduce Γ p := by
  rfl

/-- A reduced loop is unchanged by normalisation. -/
@[simp] theorem ofPath_val (p : ReducedLoop Γ v) : ofPath p.1 = p := by
  apply Subtype.ext
  exact Path.reduce_eq_self_of_isReduced Γ p.1 p.2

noncomputable instance : Group (ReducedLoop Γ v) where
  one := ofPath Quiver.Path.nil
  mul p q := ofPath (p.1.comp q.1)
  inv p := ofPath p.1.reverse
  one_mul p := by
    apply Subtype.ext
    -- Unfold the group operation to expose the underlying normalised path.
    change (ofPath ((ofPath Quiver.Path.nil).1.comp p.1)).1 = p.1
    rw [val_ofPath, val_ofPath, Path.reduce_nil, Quiver.Path.nil_comp]
    exact Path.reduce_eq_self_of_isReduced Γ p.1 p.2
  mul_one p := by
    apply Subtype.ext
    -- Unfold the group operation to expose the underlying normalised path.
    change (ofPath (p.1.comp (ofPath Quiver.Path.nil).1)).1 = p.1
    rw [val_ofPath, val_ofPath, Path.reduce_nil, Quiver.Path.comp_nil]
    exact Path.reduce_eq_self_of_isReduced Γ p.1 p.2
  mul_assoc p q r := by
    apply Subtype.ext
    -- The two sides are normalisations of the two parenthesisations of path composition.
    change Path.reduce Γ ((Path.reduce Γ (p.1.comp q.1)).comp r.1) =
      Path.reduce Γ (p.1.comp (Path.reduce Γ (q.1.comp r.1)))
    rw [Path.reduce_comp_reduce_left, Path.reduce_comp_reduce_right,
      Quiver.Path.comp_assoc]
  inv_mul_cancel p := by
    apply Subtype.ext
    -- Unfold the inverse and product to apply cancellation of a reversed path.
    change Path.reduce Γ ((Path.reduce Γ p.1.reverse).comp p.1) =
      Path.reduce Γ Quiver.Path.nil
    rw [Path.reduce_comp_reduce_left]
    have h := Path.homotopic_comp_reverse Γ p.1.reverse
    simpa only [Quiver.Path.reverse_reverse] using h.reduce_eq Γ

@[simp] theorem val_one : (1 : ReducedLoop Γ v).1 = Quiver.Path.nil := by
  exact Path.reduce_nil Γ v

@[simp] theorem val_mul (p q : ReducedLoop Γ v) :
    (p * q).1 = Path.reduce Γ (p.1.comp q.1) := rfl

@[simp] theorem val_inv (p : ReducedLoop Γ v) :
    p⁻¹.1 = Path.reduce Γ p.1.reverse := rfl

/-- The group product agrees with concatenation of arbitrary closed paths. -/
theorem ofPath_comp (p q : Γ.Path v v) :
    ofPath (p.comp q) = ofPath p * ofPath q := by
  apply Subtype.ext
  -- The product first normalises its two factors; both normalisations are immaterial.
  change Path.reduce Γ (p.comp q) =
    Path.reduce Γ ((Path.reduce Γ p).comp (Path.reduce Γ q))
  rw [Path.reduce_comp_reduce_left, Path.reduce_comp_reduce_right]

/-- Two closed paths represent the same loop precisely when they are backtrack homotopic. -/
theorem ofPath_eq_ofPath_iff (p q : Γ.Path v v) :
    ofPath p = ofPath q ↔ Path.Homotopic Γ p q := by
  constructor
  · intro h
    apply (Path.homotopic_iff_reduce_eq Γ).2
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact (Path.homotopic_iff_reduce_eq Γ).1 h

/-- A reduced loop is the identity exactly when its path is backtrack homotopic
to the empty path. -/
theorem ofPath_eq_one_iff (p : Γ.Path v v) :
    ofPath p = 1 ↔ Path.Homotopic Γ p Quiver.Path.nil := by
  simpa only [show (1 : ReducedLoop Γ v) = ofPath Quiver.Path.nil from rfl] using
    ofPath_eq_ofPath_iff p Quiver.Path.nil

end ReducedLoop

/-- The two orientations of a rose petal give distinct elements of its reduced loop group. -/
theorem rose_petal_ne_reverse {α : Type*} (a : α) :
    (ReducedLoop.ofPath ((rose α).dart (a, true)).toPath :
      ReducedLoop (rose α) PUnit.unit) ≠
    ReducedLoop.ofPath ((rose α).dart (a, false)).toPath := by
  intro h
  exact Path.rose_not_homotopic_reverse a
    ((ReducedLoop.ofPath_eq_ofPath_iff _ _).mp h)

end TauCeti.SerreGraph
