/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.IsoClass
import Mathlib.GroupTheory.Perm.Cycle.Concrete
-- Kernel reduction of cycle types needs the unexposed cycle-factor bodies.
import all Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Counts of connected permutation triples through degree five

There are 11064 labelled connected degree-five triples, 97 simultaneous-conjugation classes,
and 461 classes with a marked label. The labelled count sums over the seven cycle types of
the first permutation. Burnside's lemma computes the unpointed count from fixed pairs in
centralizers. The marked action is free, giving the marked count without enumerating its quotient.
The corresponding labelled and marked counts in degrees two to four complete the comparison table.

## References

* TauCetiRoadmap, BelyiMaps, §6.3, the three levels of rigidification and their numerical table.
* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.5.
-/

public section
open Equiv MulAction
namespace TauCeti
namespace PermutationTriple


private def connectedFiberCount {n : ℕ} (a : Perm (Fin n)) : ℕ :=
  Fintype.card {b : Perm (Fin n) // (ofTwo a b).IsConnected}

private def connectedTripleEquivSigma (n : ℕ) :
    ConnectedTriple n ≃ Σ a : Perm (Fin n), {b : Perm (Fin n) // (ofTwo a b).IsConnected} where
  toFun t := ⟨t.1.σ0, t.1.σ1, by
    have h : ofTwo t.1.σ0 t.1.σ1 = t.1 := ext_of_two rfl rfl
    simpa only [h] using t.2⟩
  invFun x := ⟨ofTwo x.1 x.2.1, x.2.2⟩
  left_inv t := Subtype.ext (ext_of_two rfl rfl)
  right_inv _ := rfl

private theorem card_connectedTriple_eq_sum (n : ℕ) :
    Fintype.card (ConnectedTriple n) = ∑ a : Perm (Fin n), connectedFiberCount a := by
  rw [Fintype.card_congr (connectedTripleEquivSigma n), Fintype.card_sigma]
  rfl

private theorem connectedFiberCount_conj {n : ℕ} (a g : Perm (Fin n)) :
    connectedFiberCount (g * a * g⁻¹) = connectedFiberCount a := by
  apply Fintype.card_congr
  symm
  refine Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun b => ?_
  change (ofTwo a b).IsConnected ↔ (ofTwo (g * a * g⁻¹) (g * b * g⁻¹)).IsConnected
  rw [← smul_ofTwo, isConnected_smul_iff]

private theorem fiber_one : connectedFiberCount (1 : Perm (Fin 5)) = 24 := by decide +kernel
private theorem fiber_two : connectedFiberCount (c[0, 1] : Perm (Fin 5)) = 48 := by decide +kernel
private theorem fiber_three : connectedFiberCount (c[0, 1, 2] : Perm (Fin 5)) = 72 := by
  decide +kernel
private theorem fiber_two_two : connectedFiberCount (c[0, 1] * c[2, 3] : Perm (Fin 5)) = 80 := by
  decide +kernel
private theorem fiber_four : connectedFiberCount (c[0, 1, 2, 3] : Perm (Fin 5)) = 96 := by
  decide +kernel
private theorem fiber_three_two :
    connectedFiberCount (c[0, 1, 2] * c[3, 4] : Perm (Fin 5)) = 108 := by
  decide +kernel
private theorem fiber_five : connectedFiberCount (c[0, 1, 2, 3, 4] : Perm (Fin 5)) = 120 := by
  decide +kernel

private def fiveCycleReps : List (Perm (Fin 5)) :=
  [1, c[0, 1], c[0, 1, 2], c[0, 1] * c[2, 3], c[0, 1, 2, 3],
    c[0, 1, 2] * c[3, 4], c[0, 1, 2, 3, 4]]

private theorem exists_conj_fiveCycleReps : ∀ a : Perm (Fin 5),
    ∃ g : Perm (Fin 5), g * a * g⁻¹ ∈ fiveCycleReps := by decide +kernel

private def fiveFiberWeight (a : Perm (Fin 5)) : ℕ :=
  if a.cycleType = 0 then 24 else
  if a.cycleType = {2} then 48 else
  if a.cycleType = {3} then 72 else
  if a.cycleType = {2, 2} then 80 else
  if a.cycleType = {4} then 96 else
  if a.cycleType = {3, 2} then 108 else
  if a.cycleType = {5} then 120 else 0

private theorem fiveFiberWeight_conj (a g : Perm (Fin 5)) :
    fiveFiberWeight (g * a * g⁻¹) = fiveFiberWeight a := by
  simp only [fiveFiberWeight, Equiv.Perm.cycleType_conj]

private theorem sum_fiveFiberWeight : ∑ a : Perm (Fin 5), fiveFiberWeight a = 11064 := by
  decide +kernel


private def fixedPairCount {n : ℕ} (g : Perm (Fin n)) : ℕ :=
  Fintype.card {ab : {a : Perm (Fin n) // g * a * g⁻¹ = a} ×
      {b : Perm (Fin n) // g * b * g⁻¹ = b} // (ofTwo ab.1.1 ab.2.1).IsConnected}

private def fixedByEquivCentralizingPairs {n : ℕ} (g : Perm (Fin n)) :
    fixedBy (ConnectedTriple n) g ≃
    {ab : {a : Perm (Fin n) // g * a * g⁻¹ = a} ×
      {b : Perm (Fin n) // g * b * g⁻¹ = b} // (ofTwo ab.1.1 ab.2.1).IsConnected} where
  toFun t := ⟨⟨⟨t.1.1.σ0, by
    simpa only [ConnectedTriple.coe_smul, smul_σ0] using
      congrArg (fun x : ConnectedTriple n => x.1.σ0) t.2⟩,
    ⟨t.1.1.σ1, by
      simpa only [ConnectedTriple.coe_smul, smul_σ1] using
        congrArg (fun x : ConnectedTriple n => x.1.σ1) t.2⟩⟩, by
      have h : ofTwo t.1.1.σ0 t.1.1.σ1 = t.1.1 := ext_of_two rfl rfl
      simpa only [h] using t.1.2⟩
  invFun ab := ⟨⟨ofTwo ab.1.1.1 ab.1.2.1, ab.2⟩, by
    apply Subtype.ext
    apply ext_of_two
    · simpa only [ConnectedTriple.coe_smul, smul_σ0, ofTwo_σ0] using ab.1.1.2
    · simpa only [ConnectedTriple.coe_smul, smul_σ1, ofTwo_σ1] using ab.1.2.2⟩
  left_inv t := Subtype.ext (Subtype.ext (ext_of_two rfl rfl))
  right_inv ab := by apply Subtype.ext; apply Prod.ext <;> rfl

private theorem card_fixedBy_eq_fixedPairCount {n : ℕ} (g : Perm (Fin n)) :
    Fintype.card (fixedBy (ConnectedTriple n) g) = fixedPairCount g :=
  Fintype.card_congr (fixedByEquivCentralizingPairs g)

private theorem fixedPairCount_one (n : ℕ) :
    fixedPairCount (1 : Perm (Fin n)) = Fintype.card (ConnectedTriple n) := by
  rw [← card_fixedBy_eq_fixedPairCount]
  exact Fintype.card_congr
    ⟨Subtype.val, fun x => ⟨x, one_smul _ _⟩, fun _ => rfl, fun _ => rfl⟩

private theorem fixedPairCount_conj {n : ℕ} (a g : Perm (Fin n)) :
    fixedPairCount (g * a * g⁻¹) = fixedPairCount a := by
  rw [← card_fixedBy_eq_fixedPairCount, ← card_fixedBy_eq_fixedPairCount]
  symm
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv (MulAction.toPerm g) fun x => ?_
  change (a • x = x) ↔ (g * a * g⁻¹) • (g • x) = g • x
  simp only [mul_smul, inv_smul_smul, smul_left_cancel_iff]

private theorem fixed_pair_two : fixedPairCount (c[0, 1] : Perm (Fin 5)) = 0 := by decide +kernel
private theorem fixed_pair_three : fixedPairCount (c[0, 1, 2] : Perm (Fin 5)) = 0 := by
  decide +kernel
private theorem fixed_pair_two_two : fixedPairCount (c[0, 1] * c[2, 3] : Perm (Fin 5)) = 0 := by
  decide +kernel
private theorem fixed_pair_four : fixedPairCount (c[0, 1, 2, 3] : Perm (Fin 5)) = 0 := by
  decide +kernel
private theorem fixed_pair_three_two :
    fixedPairCount (c[0, 1, 2] * c[3, 4] : Perm (Fin 5)) = 0 := by
  decide +kernel
private theorem fixed_pair_five : fixedPairCount (c[0, 1, 2, 3, 4] : Perm (Fin 5)) = 24 := by
  decide +kernel


private theorem connectedFiberCount_eq_fiveFiberWeight (a : Perm (Fin 5)) :
    connectedFiberCount a = fiveFiberWeight a := by
  obtain ⟨g, hg⟩ := exists_conj_fiveCycleReps a
  have h : connectedFiberCount (g * a * g⁻¹) = fiveFiberWeight (g * a * g⁻¹) := by
    simp only [fiveCycleReps, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h
    · rw [h, fiber_one]; decide +kernel
    · rw [h, fiber_two]; decide +kernel
    · rw [h, fiber_three]; decide +kernel
    · rw [h, fiber_two_two]; decide +kernel
    · rw [h, fiber_four]; decide +kernel
    · rw [h, fiber_three_two]; decide +kernel
    · rw [h, fiber_five]; decide +kernel
  exact (connectedFiberCount_conj a g).symm.trans (h.trans (fiveFiberWeight_conj a g))

private theorem card_connectedTriple_five : Fintype.card (ConnectedTriple 5) = 11064 := by
  rw [card_connectedTriple_eq_sum]
  simp only [connectedFiberCount_eq_fiveFiberWeight]
  exact sum_fiveFiberWeight


private def fiveFixedWeight (a : Perm (Fin 5)) : ℕ :=
  if a.cycleType = 0 then 11064 else if a.cycleType = {5} then 24 else 0

private theorem fiveFixedWeight_conj (a g : Perm (Fin 5)) :
    fiveFixedWeight (g * a * g⁻¹) = fiveFixedWeight a := by
  simp only [fiveFixedWeight, Equiv.Perm.cycleType_conj]

private theorem fixedPairCount_eq_fiveFixedWeight (a : Perm (Fin 5)) :
    fixedPairCount a = fiveFixedWeight a := by
  obtain ⟨g, hg⟩ := exists_conj_fiveCycleReps a
  have h : fixedPairCount (g * a * g⁻¹) = fiveFixedWeight (g * a * g⁻¹) := by
    simp only [fiveCycleReps, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h
    · rw [h, fixedPairCount_one, card_connectedTriple_five]; decide +kernel
    · rw [h, fixed_pair_two]; decide +kernel
    · rw [h, fixed_pair_three]; decide +kernel
    · rw [h, fixed_pair_two_two]; decide +kernel
    · rw [h, fixed_pair_four]; decide +kernel
    · rw [h, fixed_pair_three_two]; decide +kernel
    · rw [h, fixed_pair_five]; decide +kernel
  exact (fixedPairCount_conj a g).symm.trans (h.trans (fiveFixedWeight_conj a g))

private theorem sum_fiveFixedWeight : ∑ a : Perm (Fin 5), fiveFixedWeight a = 11640 := by
  decide +kernel


end PermutationTriple

/-- There are 11064 labelled connected triples in degree five. -/
theorem ConnectedTriple.card_five : Fintype.card (ConnectedTriple 5) = 11064 :=
  PermutationTriple.card_connectedTriple_five

/-- There are 97 unpointed isomorphism classes of connected degree-five triples. -/
theorem ConnectedIsoClass.card_five : Fintype.card (ConnectedIsoClass 5) = 97 := by
  rw [← Nat.card_eq_fintype_card]
  let : Fintype (MulAction.orbitRel.Quotient (Perm (Fin 5)) (ConnectedTriple 5)) :=
    inferInstanceAs (Fintype (ConnectedIsoClass 5))
  have h := sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Perm (Fin 5)) (ConnectedTriple 5)
  simp only [PermutationTriple.card_fixedBy_eq_fixedPairCount,
    PermutationTriple.fixedPairCount_eq_fiveFixedWeight] at h
  rw [PermutationTriple.sum_fiveFixedWeight] at h
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  change 11640 = Nat.card (ConnectedIsoClass 5) * Nat.card (Perm (Fin 5)) at h
  rw [Nat.card_eq_fintype_card (α := Perm (Fin 5))] at h
  have hc : Fintype.card (Perm (Fin 5)) = 120 := by decide +kernel
  rw [hc] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 120) h.symm


/-- There are three labelled connected triples in degree two. -/
theorem ConnectedTriple.card_two : Fintype.card (ConnectedTriple 2) = 3 := by decide

/-- There are three pointed isomorphism classes in degree two. -/
theorem MarkedIsoClass.card_two : Nat.card (MarkedIsoClass 2) = 3 := by
  have h := card_mul_factorial 2
  rw [ConnectedTriple.card_two] at h
  norm_num [Nat.factorial] at h
  omega


theorem ConnectedTriple.card_three : Fintype.card (ConnectedTriple 3) = 26 := by
  decide +kernel

theorem ConnectedTriple.card_four : Fintype.card (ConnectedTriple 4) = 426 := by
  decide +kernel

theorem MarkedIsoClass.card_three : Nat.card (MarkedIsoClass 3) = 13 := by
  have h := MarkedIsoClass.card_mul_factorial 3
  rw [ConnectedTriple.card_three] at h
  norm_num [Nat.factorial] at h
  omega

theorem MarkedIsoClass.card_four : Nat.card (MarkedIsoClass 4) = 71 := by
  have h := MarkedIsoClass.card_mul_factorial 4
  rw [ConnectedTriple.card_four] at h
  norm_num [Nat.factorial] at h
  omega

theorem MarkedIsoClass.card_five : Nat.card (MarkedIsoClass 5) = 461 := by
  have h := MarkedIsoClass.card_mul_factorial 5
  rw [ConnectedTriple.card_five] at h
  norm_num [Nat.factorial] at h
  omega


end TauCeti
