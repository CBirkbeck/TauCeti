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
# Incidence boundaries of Serre graphs

A chosen set of darts supplies the actual edges of a directed multigraph. Its incidence map
sends an edge to its terminal vertex minus its initial vertex. Keeping the dart as the edge
index retains loops and parallel edges, even when they have the same endpoints. The integral
kernel is the lattice of cycles; reduction modulo two gives the binary cycle space.

These are the chain modules used to compare graph loops with homological cycles and to build
forest bases. No orientation or connectedness is needed for the incidence map.

## References

* A. Hatcher, *Algebraic Topology*, §2.2.
* R. Diestel, *Graph Theory*, §1.9.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph) (O : Set Γ.E)

/-- The boundary of a formal edge chain, with the convention `target - source`.
The actual edges are the darts in `O`, which may include loops or parallel edges. -/
noncomputable def incidenceBoundary (R : Type*) [Ring R] :
    (O →₀ R) →ₗ[R] (Γ.V →₀ R) :=
  Finsupp.linearCombination R fun e : O =>
    Finsupp.single (Γ.tgt e.1) 1 - Finsupp.single (Γ.src e.1) 1

/-- The incidence column of one dart is its target vertex minus its source vertex. -/
@[simp] theorem incidenceBoundary_single (R : Type*) [Ring R] (e : O) :
    Γ.incidenceBoundary O R (Finsupp.single e 1) =
      Finsupp.single (Γ.tgt e.1) 1 - Finsupp.single (Γ.src e.1) 1 := by
  simp [incidenceBoundary]

/-- The coefficient of the boundary at a vertex is incoming flow minus outgoing flow. -/
theorem incidenceBoundary_apply (R : Type*) [Ring R] (c : O →₀ R) (v : Γ.V) :
    Γ.incidenceBoundary O R c v =
      c.sum fun e a => (a •
        (Finsupp.single (Γ.tgt e.1) (1 : R) -
          Finsupp.single (Γ.src e.1) (1 : R))) v := by
  simp [incidenceBoundary, Finsupp.linearCombination_apply, Finsupp.sum_apply]

/-- The integral incidence map of a set of Serre darts. -/
noncomputable abbrev integralCycleBoundary : (O →₀ ℤ) →ₗ[ℤ] (Γ.V →₀ ℤ) :=
  Γ.incidenceBoundary O ℤ

/-- Integral cycles are exactly the integer edge chains with zero incidence boundary. -/
noncomputable def cycleLattice : Submodule ℤ (O →₀ ℤ) :=
  LinearMap.ker (Γ.integralCycleBoundary O)

/-- An integral edge chain is a cycle precisely when its boundary vanishes. -/
theorem mem_cycleLattice_iff (c : O →₀ ℤ) :
    c ∈ Γ.cycleLattice O ↔ Γ.integralCycleBoundary O c = 0 :=
  LinearMap.mem_ker

/-- The binary incidence map, still indexed by actual darts. -/
noncomputable abbrev modTwoCycleBoundary : (O →₀ ZMod 2) →ₗ[ZMod 2] (Γ.V →₀ ZMod 2) :=
  Γ.incidenceBoundary O (ZMod 2)

/-- Binary cycles are the kernel of incidence modulo two. -/
noncomputable def modTwoCycleSpace : Submodule (ZMod 2) (O →₀ ZMod 2) :=
  LinearMap.ker (Γ.modTwoCycleBoundary O)

/-- A binary edge chain is a cycle precisely when its boundary vanishes. -/
theorem mem_modTwoCycleSpace_iff (c : O →₀ ZMod 2) :
    c ∈ Γ.modTwoCycleSpace O ↔ Γ.modTwoCycleBoundary O c = 0 :=
  LinearMap.mem_ker

/-- A loop has zero incidence column over every coefficient ring. -/
@[simp] theorem incidenceBoundary_single_of_loop (R : Type*) [Ring R] (e : O)
    (he : Γ.tgt e.1 = Γ.src e.1) :
    Γ.incidenceBoundary O R (Finsupp.single e 1) = 0 := by
  simp [he]

/-- A loop gives an integral cycle, including when it is the only edge. -/
theorem single_mem_cycleLattice_of_loop (e : O) (he : Γ.tgt e.1 = Γ.src e.1) :
    Finsupp.single e (1 : ℤ) ∈ Γ.cycleLattice O := by
  rw [Γ.mem_cycleLattice_iff]
  exact Γ.incidenceBoundary_single_of_loop O ℤ e he

/-- A loop also gives a binary cycle. -/
theorem single_mem_modTwoCycleSpace_of_loop (e : O) (he : Γ.tgt e.1 = Γ.src e.1) :
    Finsupp.single e (1 : ZMod 2) ∈ Γ.modTwoCycleSpace O := by
  rw [Γ.mem_modTwoCycleSpace_iff]
  exact Γ.incidenceBoundary_single_of_loop O (ZMod 2) e he

/-- The source coefficient of a non-loop edge's incidence column is `-1`. -/
@[simp] theorem incidenceBoundary_single_apply_src (R : Type*) [Ring R]
    (e : O) (he : Γ.src e.1 ≠ Γ.tgt e.1) :
    Γ.incidenceBoundary O R (Finsupp.single e 1) (Γ.src e.1) = -1 := by
  simp [Γ.incidenceBoundary_single O R e, he]

/-- The target coefficient of a non-loop edge's incidence column is `1`. -/
@[simp] theorem incidenceBoundary_single_apply_tgt (R : Type*) [Ring R]
    (e : O) (he : Γ.src e.1 ≠ Γ.tgt e.1) :
    Γ.incidenceBoundary O R (Finsupp.single e 1) (Γ.tgt e.1) = 1 := by
  simp [Γ.incidenceBoundary_single O R e, he]

/-- A single non-loop edge is not an integral cycle. -/
theorem single_notMem_cycleLattice_of_ne (e : O) (he : Γ.src e.1 ≠ Γ.tgt e.1) :
    Finsupp.single e (1 : ℤ) ∉ Γ.cycleLattice O := by
  rw [Γ.mem_cycleLattice_iff]
  intro h
  have hv := congrArg (fun c : Γ.V →₀ ℤ => c (Γ.src e.1)) h
  rw [Γ.incidenceBoundary_single_apply_src O ℤ e he] at hv
  simp at hv

/-- A single non-loop edge is not a binary cycle. -/
theorem single_notMem_modTwoCycleSpace_of_ne (e : O) (he : Γ.src e.1 ≠ Γ.tgt e.1) :
    Finsupp.single e (1 : ZMod 2) ∉ Γ.modTwoCycleSpace O := by
  rw [Γ.mem_modTwoCycleSpace_iff]
  intro h
  have hv := congrArg (fun c : Γ.V →₀ ZMod 2 => c (Γ.src e.1)) h
  rw [Γ.incidenceBoundary_single_apply_src O (ZMod 2) e he] at hv
  simp at hv

/-- Parallel oriented edges have the same incidence column. This includes parallel loops. -/
theorem incidenceBoundary_single_eq_of_parallel (R : Type*) [Ring R]
    (e f : O) (hs : Γ.src e.1 = Γ.src f.1) (ht : Γ.tgt e.1 = Γ.tgt f.1) :
    Γ.incidenceBoundary O R (Finsupp.single e 1) =
      Γ.incidenceBoundary O R (Finsupp.single f 1) := by
  simp [hs, ht]

/-- Reversing a dart negates its integral incidence column. Both darts must be in `O`. -/
theorem integralCycleBoundary_single_rev (e f : O) (hf : f.1 = Γ.rev e.1) :
    Γ.integralCycleBoundary O (Finsupp.single f 1) =
      -Γ.integralCycleBoundary O (Finsupp.single e 1) := by
  simp [hf, sub_eq_add_neg, add_comm]

/-- Reversing a dart leaves its binary incidence column unchanged. -/
theorem modTwoCycleBoundary_single_rev (e f : O) (hf : f.1 = Γ.rev e.1) :
    Γ.modTwoCycleBoundary O (Finsupp.single f 1) =
      Γ.modTwoCycleBoundary O (Finsupp.single e 1) := by
  simp [hf, ZModModule.sub_eq_add, add_comm]

/-- The signed difference of two parallel edges is an integral cycle. -/
theorem sub_single_mem_cycleLattice_of_parallel (e f : O)
    (hs : Γ.src e.1 = Γ.src f.1) (ht : Γ.tgt e.1 = Γ.tgt f.1) :
    Finsupp.single e (1 : ℤ) - Finsupp.single f 1 ∈ Γ.cycleLattice O := by
  rw [Γ.mem_cycleLattice_iff, map_sub,
    Γ.incidenceBoundary_single_eq_of_parallel O ℤ e f hs ht, sub_self]

/-- Distinct parallel edges give a nonzero integral cycle. -/
theorem sub_single_ne_zero_of_ne (e f : O) (hef : e ≠ f) :
    Finsupp.single e (1 : ℤ) - Finsupp.single f 1 ≠ 0 := by
  intro h
  have hv := congrArg (fun c : O →₀ ℤ => c e) h
  simp [hef] at hv

/-- The sum of two parallel edges is a binary cycle, since signs disappear modulo two. -/
theorem add_single_mem_modTwoCycleSpace_of_parallel (e f : O)
    (hs : Γ.src e.1 = Γ.src f.1) (ht : Γ.tgt e.1 = Γ.tgt f.1) :
    Finsupp.single e (1 : ZMod 2) + Finsupp.single f 1 ∈ Γ.modTwoCycleSpace O := by
  rw [Γ.mem_modTwoCycleSpace_iff, map_add,
    Γ.incidenceBoundary_single_eq_of_parallel O (ZMod 2) e f hs ht]
  rw [← two_smul (ZMod 2)
    (Γ.modTwoCycleBoundary O (Finsupp.single f (1 : ZMod 2)))]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

end SerreGraph
end TauCeti
