/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.ZMod.Basic

/-!
# Incidence boundaries and cycle modules of Serre graphs

For any chosen set of darts, the signed incidence boundary sends a dart from `u` to `v` to
`δ_v - δ_u`. Its integral kernel is the lattice of finite integral cycles. The same construction
over `ZMod 2` gives the binary cycle space; its boundary sends an edge to the sum of its endpoints.
A loop has zero boundary over either ring, while parallel edges remain separate coordinates.

The edge coordinates are the actual chosen darts. In particular, an orientation chooses one dart
from each reversal pair, but the construction also works for an arbitrary subset of darts. These
modules are the input to spanning-forest cycle bases and to the comparison with graph path groups.

## References

* A. Hatcher, *Algebraic Topology*, §2.2 (cellular incidence boundaries).
* R. Diestel, *Graph Theory*, §1.9 (binary cycle spaces).
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph) (O : Set Γ.E)

/-- The signed incidence boundary of a finitely supported edge chain. A chosen dart is an edge
coordinate even when its reverse is chosen as well. -/
noncomputable def incidenceBoundary (R : Type*) [Ring R] :
    (O →₀ R) →ₗ[R] (Γ.V →₀ R) :=
  Finsupp.linearCombination R fun e => Finsupp.single (Γ.tgt e.1) 1 -
    Finsupp.single (Γ.src e.1) 1

/-- The integral incidence boundary of the chosen darts. -/
noncomputable abbrev integralCycleBoundary : (O →₀ ℤ) →ₗ[ℤ] (Γ.V →₀ ℤ) :=
  Γ.incidenceBoundary O ℤ

/-- Finite integral edge chains with zero incidence boundary. -/
noncomputable def cycleLattice : Submodule ℤ (O →₀ ℤ) :=
  (Γ.integralCycleBoundary O).ker

/-- The binary incidence boundary of the chosen darts. -/
noncomputable abbrev modTwoCycleBoundary : (O →₀ ZMod 2) →ₗ[ZMod 2] (Γ.V →₀ ZMod 2) :=
  Γ.incidenceBoundary O (ZMod 2)

/-- The binary cycle space, with actual darts as its edge coordinates. -/
noncomputable def modTwoCycleSpace : Submodule (ZMod 2) (O →₀ ZMod 2) :=
  (Γ.modTwoCycleBoundary O).ker

variable {Γ O}

@[simp] theorem incidenceBoundary_single (R : Type*) [Ring R] (e : O) (r : R) :
    Γ.incidenceBoundary O R (Finsupp.single e r) =
      r • (Finsupp.single (Γ.tgt e.1) 1 - Finsupp.single (Γ.src e.1) 1) := by
  simp [incidenceBoundary]

/-- A chain is an integral cycle exactly when its signed incidence boundary vanishes. -/
theorem mem_cycleLattice_iff (c : O →₀ ℤ) :
    c ∈ Γ.cycleLattice O ↔ Γ.integralCycleBoundary O c = 0 :=
  LinearMap.mem_ker

/-- A binary chain is a cycle exactly when its incidence boundary vanishes. -/
theorem mem_modTwoCycleSpace_iff (c : O →₀ ZMod 2) :
    c ∈ Γ.modTwoCycleSpace O ↔ Γ.modTwoCycleBoundary O c = 0 :=
  LinearMap.mem_ker

/-- A loop is an integral cycle, for either choice of its orientation. -/
theorem single_mem_cycleLattice_of_loop (e : O) (h : Γ.src e.1 = Γ.tgt e.1) :
    Finsupp.single e (1 : ℤ) ∈ Γ.cycleLattice O := by
  rw [mem_cycleLattice_iff, incidenceBoundary_single, one_smul, ← h, sub_self]

/-- A loop is also a binary cycle. -/
theorem single_mem_modTwoCycleSpace_of_loop (e : O) (h : Γ.src e.1 = Γ.tgt e.1) :
    Finsupp.single e (1 : ZMod 2) ∈ Γ.modTwoCycleSpace O := by
  rw [mem_modTwoCycleSpace_iff, incidenceBoundary_single, one_smul, ← h, sub_self]

/-- An individual dart is an integral cycle exactly when it is a loop. -/
theorem single_mem_cycleLattice_iff (e : O) :
    Finsupp.single e (1 : ℤ) ∈ Γ.cycleLattice O ↔ Γ.src e.1 = Γ.tgt e.1 := by
  refine ⟨fun h => ?_, single_mem_cycleLattice_of_loop e⟩
  by_contra hne
  have hb := (mem_cycleLattice_iff (Γ := Γ) (O := O) _).mp h
  have hs := congrArg (fun c : Γ.V →₀ ℤ => c (Γ.src e.1)) hb
  simp [Ne.symm hne] at hs

/-- An individual dart is a binary cycle exactly when it is a loop. -/
theorem single_mem_modTwoCycleSpace_iff (e : O) :
    Finsupp.single e (1 : ZMod 2) ∈ Γ.modTwoCycleSpace O ↔ Γ.src e.1 = Γ.tgt e.1 := by
  refine ⟨fun h => ?_, single_mem_modTwoCycleSpace_of_loop e⟩
  by_contra hne
  have hb := (mem_modTwoCycleSpace_iff (Γ := Γ) (O := O) _).mp h
  have hs := congrArg (fun c : Γ.V →₀ ZMod 2 => c (Γ.src e.1)) hb
  simp [Ne.symm hne] at hs

/-- Reversing a dart negates its signed incidence column. -/
theorem incidenceBoundary_rev (R : Type*) [Ring R] (e : Γ.E)
    (he : e ∈ O) (hre : Γ.rev e ∈ O) :
    Γ.incidenceBoundary O R (Finsupp.single ⟨Γ.rev e, hre⟩ 1) =
      -Γ.incidenceBoundary O R (Finsupp.single ⟨e, he⟩ 1) := by
  simp [Γ.tgt_rev, Γ.src_rev, neg_sub]

/-- In characteristic two the direction of a dart does not change its incidence column. -/
theorem modTwoCycleBoundary_rev (e : Γ.E) (he : e ∈ O) (hre : Γ.rev e ∈ O) :
    Γ.modTwoCycleBoundary O (Finsupp.single ⟨Γ.rev e, hre⟩ 1) =
      Γ.modTwoCycleBoundary O (Finsupp.single ⟨e, he⟩ 1) := by
  calc
    _ = -Γ.modTwoCycleBoundary O (Finsupp.single ⟨e, he⟩ 1) :=
      incidenceBoundary_rev (R := ZMod 2) e he hre
    _ = _ := by
      ext v
      simp [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_comm]

end SerreGraph
end TauCeti
