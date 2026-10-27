/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Product

/-!
# Intersections read by products of folded graphs

Reduced closed paths in a folded graph have canonical label words. Two loops representing
the same free-group element therefore pair to a loop in the labelled product, which reads
the intersection of the two accepted subgroups.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 9, Proposition 9.4.
-/

public section

namespace TauCeti
namespace StallingsGraph

universe u v w x y

variable {α : Type u}

/-- The product of folded labelled graphs reads exactly the intersection of their
accepted subgroups, at every pair of vertices. -/
theorem prod_subgroup {S : StallingsGraph.{u, v, w} α}
    {T : StallingsGraph.{u, x, y} α} (hS : S.IsFolded) (hT : T.IsFolded)
    (a : S.graph.V) (b : T.graph.V) :
    (S.prod T).subgroup (a, b) = S.subgroup a ⊓ T.subgroup b := by
  classical
  apply le_antisymm (prod_subgroup_le S T a b)
  intro g hg
  obtain ⟨hgS, hgT⟩ := hg
  obtain ⟨p, hp, hpg⟩ := (S.mem_subgroup_iff_exists_reduced_path).mp hgS
  obtain ⟨q, hq, hqg⟩ := (T.mem_subgroup_iff_exists_reduced_path).mp hgT
  have hword : S.word p = T.word q := by
    calc
      S.word p = (S.read p).toWord := (IsFolded.toWord_read_eq_word S hS p hp).symm
      _ = g.toWord := by rw [hpg]
      _ = (T.read q).toWord := by rw [hqg]
      _ = T.word q := IsFolded.toWord_read_eq_word T hT q hq
  obtain ⟨r, hrS, _⟩ := exists_prod_path_of_word_eq S T p q hword
  apply (S.prod T).mem_subgroup_iff.mpr
  refine ⟨r, ?_⟩
  calc
    (S.prod T).read r = S.read ((S.prodFst T).graphHom.toPrefunctor.mapPath r) :=
      ((S.prodFst T).read_mapPath r).symm
    _ = S.read p := congrArg S.read hrS
    _ = g := hpg

end StallingsGraph
end TauCeti
