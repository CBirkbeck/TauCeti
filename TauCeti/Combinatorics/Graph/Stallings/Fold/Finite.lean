/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Fold.Subgroup
public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import Mathlib.Data.Fintype.EquivFin

/-!
# Finite folding of labelled graphs

Repeatedly identifying two outgoing darts with the same label terminates for a finite
labelled graph: each nontrivial fold strictly reduces its number of darts. The resulting
quotient is folded, retains the accepted subgroup, and preserves connectedness. This is the
finite folding step used to construct subgroup graphs from finite generating families.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 2, Lemma 2.5 and Section 3, Proposition 3.8.
-/

public section

namespace TauCeti.StallingsGraph

universe u v w

variable {α : Type u}

/-- Every finite labelled graph has a finite folded quotient with the same accepted subgroup.
The quotient map is surjective on vertices and darts, so connected input remains connected. -/
theorem exists_folded_quotient (S : StallingsGraph.{u, v, w} α)
    [Finite S.graph.V] [Finite S.graph.E] :
    ∃ (T : StallingsGraph.{u, v, w} α),
      Finite T.graph.V ∧ Finite T.graph.E ∧
        ∃ f : S.Hom T, T.IsFolded ∧
          Function.Surjective f.graphHom.mapV ∧
          Function.Surjective f.graphHom.mapE ∧
          T.subgroup T.base = S.subgroup S.base ∧
          (S.graph.Connected → T.graph.Connected) := by
  classical
  let card (R : StallingsGraph.{u, v, w} α) [Finite R.graph.E] : ℕ :=
    @Fintype.card R.graph.E (Fintype.ofFinite R.graph.E)
  suffices h : ∀ (n : ℕ) (S : StallingsGraph.{u, v, w} α)
      [Finite S.graph.V] [Finite S.graph.E], card S = n →
      ∃ (T : StallingsGraph.{u, v, w} α),
        Finite T.graph.V ∧ Finite T.graph.E ∧
          ∃ f : S.Hom T, T.IsFolded ∧
            Function.Surjective f.graphHom.mapV ∧
            Function.Surjective f.graphHom.mapE ∧
            T.subgroup T.base = S.subgroup S.base from by
    obtain ⟨T, hTv, hTe, f, hfold, hv, he, hsub⟩ := h (card S) S rfl
    exact ⟨T, hTv, hTe, f, hfold, hv, he, hsub,
      fun hS => f.graphHom.connected_of_surjective hv hS⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S _ _ hn
    by_cases hfold : S.IsFolded
    · refine ⟨S, inferInstance, inferInstance, Hom.id S, hfold, ?_, ?_, rfl⟩
      · simpa only [Hom.id_graphHom, SerreGraph.Hom.id_mapV] using
          (Function.surjective_id : Function.Surjective (id : S.graph.V → S.graph.V))
      · simpa only [Hom.id_graphHom, SerreGraph.Hom.id_mapE] using
          (Function.surjective_id : Function.Surjective (id : S.graph.E → S.graph.E))
    · rw [S.isFolded_def] at hfold
      push Not at hfold
      obtain ⟨e₁, e₂, hs, hl, hne⟩ := hfold
      let F := S.foldAt e₁ e₂ hs hl
      let φ := S.foldHom e₁ e₂ hs hl
      have hlt : card F < n := by
        rw [← hn]
        exact @Fintype.card_lt_of_surjective_not_injective _ _
          (Fintype.ofFinite S.graph.E) (Fintype.ofFinite F.graph.E)
          φ.graphHom.mapE (S.foldHom_mapE_surjective e₁ e₂ hs hl)
          (fun hi => hne (hi (S.foldHom_mapE_eq e₁ e₂ hs hl)))
      obtain ⟨T, hTv, hTe, ψ, hT, hψv, hψe, hsub⟩ :=
        ih (card F) hlt F rfl
      refine ⟨T, hTv, hTe, Hom.comp ψ φ, hT, ?_, ?_, ?_⟩
      · simpa only [Hom.comp_graphHom, SerreGraph.Hom.comp_mapV] using
          hψv.comp (S.foldHom_mapV_surjective e₁ e₂ hs hl)
      · simpa only [Hom.comp_graphHom, SerreGraph.Hom.comp_mapE] using
          hψe.comp (S.foldHom_mapE_surjective e₁ e₂ hs hl)
      · exact hsub.trans (S.foldAt_subgroup_base e₁ e₂ hs hl)

end TauCeti.StallingsGraph
