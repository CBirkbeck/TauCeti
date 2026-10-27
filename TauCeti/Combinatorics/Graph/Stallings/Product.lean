/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Folded

/-!
# Products of labelled graphs

The product of two based labelled Serre graphs pairs darts carrying the same signed letter.
Its closed paths project to closed paths in both factors, so its accepted subgroup lies in
their intersection. Foldedness is preserved by the product.

The construction is the fibre product over the labelled rose used in Stallings' subgroup
intersection method.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*, Section 9.
-/

public section

namespace TauCeti
namespace StallingsGraph

universe u v w x y

variable {α : Type u}

/-- The based fibre product of labelled graphs: vertices are pairs and darts are pairs
with identical signed labels. -/
@[expose] def prod (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) : StallingsGraph α where
  graph := {
    V := S.graph.V × T.graph.V
    E := {e : S.graph.E × T.graph.E // S.label e.1 = T.label e.2}
    src := fun e => (S.graph.src e.1.1, T.graph.src e.1.2)
    rev := fun e => ⟨(S.graph.rev e.1.1, T.graph.rev e.1.2), by
      simpa only [S.label_rev, T.label_rev] using congrArg
        (fun l : α × Bool => (l.1, !l.2)) e.2⟩
    rev_rev := by
      intro e
      apply Subtype.ext
      simp
    rev_ne := by
      intro e h
      have hfst : S.graph.rev e.1.1 = e.1.1 :=
        congrArg (fun p : S.graph.E × T.graph.E => p.1) (congrArg Subtype.val h)
      exact S.graph.rev_ne e.1.1 hfst }
  base := (S.base, T.base)
  label := fun e => S.label e.1.1
  label_rev := by
    intro e
    exact S.label_rev e.1.1

@[simp] theorem prod_base (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) : (S.prod T).base = (S.base, T.base) := rfl

@[simp] theorem prod_label (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (e : (S.prod T).graph.E) :
    (S.prod T).label e = S.label e.1.1 := rfl

/-- The first projection preserves the base point and labels. -/
@[expose] def prodFst (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) : (S.prod T).Hom S where
  graphHom := {
    mapV := Prod.fst
    mapE := fun e => e.1.1
    map_src := by intro e; rfl
    map_rev := by intro e; rfl }
  map_base := rfl
  map_label := by intro e; rfl

/-- The second projection preserves the base point and labels. -/
@[expose] def prodSnd (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) : (S.prod T).Hom T where
  graphHom := {
    mapV := Prod.snd
    mapE := fun e => e.1.2
    map_src := by intro e; rfl
    map_rev := by intro e; rfl }
  map_base := rfl
  map_label := by intro e; exact e.2.symm

@[simp] theorem prodFst_mapV (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (p : (S.prod T).graph.V) :
    (S.prodFst T).graphHom.mapV p = p.1 := rfl

@[simp] theorem prodSnd_mapV (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (p : (S.prod T).graph.V) :
    (S.prodSnd T).graphHom.mapV p = p.2 := rfl

@[simp] theorem prodFst_mapE (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (e : (S.prod T).graph.E) :
    (S.prodFst T).graphHom.mapE e = e.1.1 := rfl

@[simp] theorem prodSnd_mapE (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (e : (S.prod T).graph.E) :
    (S.prodSnd T).graphHom.mapE e = e.1.2 := rfl

/-- Every word read in the product is read in each factor. -/
theorem prod_subgroup_le (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) :
    (S.prod T).subgroup (S.prod T).base ≤
      S.subgroup S.base ⊓ T.subgroup T.base := by
  exact le_inf (S.prodFst T).subgroup_le (S.prodSnd T).subgroup_le

/-- Paths with the same sequence of signed labels pair to a path in the product. -/
theorem exists_prod_path_of_word_eq (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α)
    {a b : S.graph.V} {c d : T.graph.V}
    (p : S.graph.Path a b) (q : T.graph.Path c d)
    (h : S.word p = T.word q) :
    ∃ r : (S.prod T).graph.Path (a, c) (b, d),
      (S.prodFst T).graphHom.toPrefunctor.mapPath r = p ∧
      (S.prodSnd T).graphHom.toPrefunctor.mapPath r = q := by
  induction p generalizing c d q with
  | nil =>
    cases q with
    | nil => exact ⟨.nil, rfl, rfl⟩
    | cons q f => simp at h
  | cons p e ih =>
    cases q with
    | nil => simp at h
    | cons q f =>
      simp only [word_cons] at h
      obtain ⟨hpq, hef⟩ := List.append_inj' h (by simp)
      simp only [List.singleton_inj] at hef
      obtain ⟨r, hrS, hrT⟩ := ih q hpq
      refine ⟨r.cons ⟨⟨(e.1, f.1), hef⟩, ?_, ?_⟩, ?_, ?_⟩
      · exact Prod.ext e.2.1 f.2.1
      · have he := e.2.2
        have hf := f.2.2
        rw [S.graph.tgt_def] at he
        rw [T.graph.tgt_def] at hf
        simpa only [SerreGraph.tgt_def, prod] using Prod.ext he hf
      · simpa [Prefunctor.mapPath, prodFst, SerreGraph.Hom.toPrefunctor] using
          congrArg (fun z => z.cons e) hrS
      · simpa [Prefunctor.mapPath, prodSnd, SerreGraph.Hom.toPrefunctor] using
          congrArg (fun z => z.cons f) hrT

/-- A product of folded labelled graphs is folded. -/
theorem IsFolded.prod {S : StallingsGraph.{u, v, w} α}
    {T : StallingsGraph.{u, x, y} α} (hS : S.IsFolded) (hT : T.IsFolded) :
    (S.prod T).IsFolded := by
  simp only [isFolded_def] at hS hT ⊢
  intro e f hsrc hlabel
  apply Subtype.ext
  apply Prod.ext
  · apply hS e.1.1 f.1.1 (congrArg Prod.fst hsrc) hlabel
  · exact hT e.1.2 f.1.2 (congrArg Prod.snd hsrc) (e.2.symm.trans (hlabel.trans f.2))

/-- Each labelled graph maps into its product with the rose on the right. -/
def prodRoseHom (S : StallingsGraph.{u, v, w} α) :
    S.Hom (S.prod (rose α)) where
  graphHom := {
    mapV := fun a => (a, PUnit.unit)
    mapE := fun e => ⟨(e, S.label e), rfl⟩
    map_src := by intro e; rfl
    map_rev := by
      intro e
      apply Subtype.ext
      exact Prod.ext rfl (S.label_rev e) }
  map_base := rfl
  map_label := by intro e; rfl

/-- The rose imposes no additional restriction on accepted words. -/
theorem prod_rose_subgroup (S : StallingsGraph.{u, v, w} α) :
    (S.prod (rose α)).subgroup (S.prod (rose α)).base = S.subgroup S.base := by
  apply le_antisymm
  · exact (S.prodFst (rose α)).subgroup_le
  · exact (S.prodRoseHom).subgroup_le

/-- Each labelled graph maps into its product with the rose on the left. -/
def roseProdHom (S : StallingsGraph.{u, v, w} α) :
    S.Hom ((rose α).prod S) where
  graphHom := {
    mapV := fun a => (PUnit.unit, a)
    mapE := fun e => ⟨(S.label e, e), rfl⟩
    map_src := by intro e; rfl
    map_rev := by
      intro e
      apply Subtype.ext
      exact Prod.ext (S.label_rev e) rfl }
  map_base := rfl
  map_label := by intro e; rfl

/-- A rose in the first factor imposes no additional restriction on accepted words. -/
theorem rose_prod_subgroup (S : StallingsGraph.{u, v, w} α) :
    ((rose α).prod S).subgroup ((rose α).prod S).base = S.subgroup S.base := by
  apply le_antisymm
  · exact ((rose α).prodSnd S).subgroup_le
  · exact (S.roseProdHom).subgroup_le

end StallingsGraph
end TauCeti
