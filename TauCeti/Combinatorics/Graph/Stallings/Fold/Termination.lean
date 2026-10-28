/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Fold.Subgroup
public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite Stallings folding

A fold of two distinct equally labelled darts strictly decreases the number of darts.
Consequently a finite labelled graph admits a finite sequence of folds ending in a folded
graph. Every step preserves the subgroup read at the base vertex. This is the termination
step in the construction of a finite folded graph from a flower of generating words.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 3, Proposition 3.8.
-/

public section

namespace TauCeti.StallingsGraph

universe u v w

variable {α : Type u}

/-- A finite sequence of Stallings folds, including the empty sequence. -/
inductive FoldSequence (S : StallingsGraph.{u, v, w} α) :
    StallingsGraph.{u, v, w} α → Prop
  | refl : FoldSequence S S
  | fold {T : StallingsGraph.{u, v, w} α} (h : FoldSequence S T)
      (e f : T.graph.E) (hne : e ≠ f)
      (hsrc : T.graph.src e = T.graph.src f)
      (hlabel : T.label e = T.label f) :
      FoldSequence S (T.foldAt e f hsrc hlabel)

/-- Concatenating two finite fold sequences gives a finite fold sequence. -/
theorem FoldSequence.trans {S T U : StallingsGraph.{u, v, w} α}
    (hST : FoldSequence S T) (hTU : FoldSequence T U) : FoldSequence S U := by
  induction hTU with
  | refl => exact hST
  | fold h e f hne hsrc hlabel ih => exact .fold ih e f hne hsrc hlabel

/-- A finite fold sequence preserves the subgroup accepted at the base vertex. -/
theorem FoldSequence.subgroup_base {S T : StallingsGraph.{u, v, w} α}
    (h : FoldSequence S T) : T.subgroup T.base = S.subgroup S.base := by
  induction h with
  | refl => rfl
  | fold h e f hne hsrc hlabel ih =>
    exact (foldAt_subgroup_base _ e f hsrc hlabel).trans ih

/-- A finite fold sequence preserves finiteness of vertices and darts. -/
theorem FoldSequence.finite {S T : StallingsGraph.{u, v, w} α}
    (h : FoldSequence S T) [Finite S.graph.V] [Finite S.graph.E] :
    Finite T.graph.V ∧ Finite T.graph.E := by
  induction h with
  | refl => exact ⟨inferInstance, inferInstance⟩
  | fold h e f hne hsrc hlabel ih =>
    let _ := ih.1
    let _ := ih.2
    exact ⟨inferInstance, inferInstance⟩

/-- A fold of a connected labelled graph remains connected. -/
theorem connected_foldAt (S : StallingsGraph.{u, v, w} α)
    (hS : S.graph.Connected) (e f : S.graph.E)
    (hsrc : S.graph.src e = S.graph.src f)
    (hlabel : S.label e = S.label f) :
    (S.foldAt e f hsrc hlabel).graph.Connected := by
  let Q := S.foldAt e f hsrc hlabel
  apply (SerreGraph.connected_iff Q.graph).2
  refine ⟨⟨Q.base⟩, (SerreGraph.preconnected_iff Q.graph).2 ?_⟩
  intro a b
  obtain ⟨x, rfl⟩ := S.foldHom_mapV_surjective e f hsrc hlabel a
  obtain ⟨y, rfl⟩ := S.foldHom_mapV_surjective e f hsrc hlabel b
  obtain ⟨p⟩ := (SerreGraph.preconnected_iff S.graph).1
    ((SerreGraph.connected_iff S.graph).1 hS).2 x y
  exact ⟨(S.foldHom e f hsrc hlabel).graphHom.toPrefunctor.mapPath p⟩

/-- A finite fold sequence preserves connectedness. -/
theorem FoldSequence.connected {S T : StallingsGraph.{u, v, w} α}
    (h : FoldSequence S T) (hS : S.graph.Connected) : T.graph.Connected := by
  induction h with
  | refl => exact hS
  | fold h e f hne hsrc hlabel ih =>
    exact connected_foldAt _ ih e f hsrc hlabel

/-- Folding distinct darts strictly decreases the number of darts. -/
theorem card_foldAt_lt (S : StallingsGraph.{u, v, w} α) [Finite S.graph.E]
    (e f : S.graph.E) (hne : e ≠ f)
    (hsrc : S.graph.src e = S.graph.src f)
    (hlabel : S.label e = S.label f) :
    Nat.card (S.foldAt e f hsrc hlabel).graph.E < Nat.card S.graph.E := by
  classical
  let _ := Fintype.ofFinite S.graph.E
  let _ := Fintype.ofFinite (S.foldAt e f hsrc hlabel).graph.E
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_surjective_not_injective
    (S.foldHom e f hsrc hlabel).graphHom.mapE
    (S.foldHom_mapE_surjective e f hsrc hlabel)
  intro hinj
  exact hne (hinj (S.foldHom_mapE_eq e f hsrc hlabel))

/-- A finite labelled graph can be folded by a finite sequence of quotients. -/
theorem exists_foldSequence_isFolded (S : StallingsGraph.{u, v, w} α)
    [Finite S.graph.V] [Finite S.graph.E] :
    ∃ T : StallingsGraph.{u, v, w} α, FoldSequence S T ∧ T.IsFolded := by
  classical
  have aux : ∀ n : ℕ, ∀ (R : StallingsGraph.{u, v, w} α),
      [Finite R.graph.V] → [Finite R.graph.E] →
      Nat.card R.graph.E = n →
      ∃ T : StallingsGraph.{u, v, w} α, FoldSequence R T ∧ T.IsFolded := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R _ _ hn
      by_cases hR : R.IsFolded
      · exact ⟨R, .refl, hR⟩
      · rw [R.isFolded_def] at hR
        push Not at hR
        obtain ⟨e, f, hsrc, hlabel, hne⟩ := hR
        let Q := R.foldAt e f hsrc hlabel
        have hlt : Nat.card Q.graph.E < n := by
          exact hn ▸ R.card_foldAt_lt e f hne hsrc hlabel
        obtain ⟨T, hchain, hfolded⟩ := ih _ hlt Q rfl
        have hstep : FoldSequence R Q := .fold .refl e f hne hsrc hlabel
        exact ⟨T, hstep.trans hchain, hfolded⟩
  exact aux (Nat.card S.graph.E) S rfl

/-- The folded quotient obtained by finite folding accepts exactly the original subgroup. -/
theorem exists_folded_subgroup (S : StallingsGraph.{u, v, w} α)
    [Finite S.graph.V] [Finite S.graph.E] :
    ∃ T : StallingsGraph.{u, v, w} α,
      FoldSequence S T ∧ T.IsFolded ∧
        T.subgroup T.base = S.subgroup S.base := by
  obtain ⟨T, h, hT⟩ := S.exists_foldSequence_isFolded
  exact ⟨T, h, hT, h.subgroup_base⟩

end TauCeti.StallingsGraph
