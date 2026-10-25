/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.MaximalSpectrum
public import TauCeti.RingTheory.Affinoid.Integral

/-!
# Jacobsonness at the boundaries of the affinoid definition

The zero ideal, the unit ideal and dual numbers give unchanged, zero-ring and nonreduced
quotients allowed by the algebraic affinoid predicate. These examples apply the affinoid
Jacobson theorem without assuming a quotient is nonzero or reduced. In the dual-number
example, Mathlib's monic polynomial quotient calculation verifies that the square-zero
generator is nonzero.
-/

public section

namespace TauCeti.Examples.Affinoid
open Polynomial TauCeti

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
local notation "T" => MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin 1 => (1 : ℝ))

/-- Quotienting the one-variable Tate algebra by zero retains Jacobsonness. -/
theorem isJacobsonRing_quotient_zero : IsJacobsonRing (T ⧸ (⊥ : Ideal T)) :=
  ((isAffinoidAlgebra_tate (K := K) (σ := Fin 1)).quotient ⊥).isJacobsonRing

/-- The quotient by the unit ideal is a Jacobson ring and is the zero ring. -/
theorem isJacobsonRing_quotient_one :
    IsJacobsonRing (T ⧸ Ideal.span {(1 : T)}) ∧
    Subsingleton (T ⧸ Ideal.span {(1 : T)}) := by
  rw [Ideal.span_singleton_one]
  exact ⟨((isAffinoidAlgebra_tate (K := K) (σ := Fin 1)).quotient ⊤).isJacobsonRing,
    inferInstance⟩

variable (F : Type*) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]

/-- Dual numbers are Jacobson although their square-zero generator is nonzero. -/
theorem isJacobsonRing_dualNumbers : IsJacobsonRing (AdjoinRoot ((X : F[X]) ^ 2)) ∧
    AdjoinRoot.root ((X : F[X]) ^ 2) ≠ 0 ∧
    AdjoinRoot.root ((X : F[X]) ^ 2) ^ 2 = 0 := by
  have : Module.Finite F (AdjoinRoot ((X : F[X]) ^ 2)) := (monic_X_pow 2).finite_adjoinRoot
  have ha : IsAffinoidAlgebra F (AdjoinRoot ((X : F[X]) ^ 2)) :=
    (isAffinoidAlgebra_self (K := F)).of_finite
  refine ⟨ha.isJacobsonRing, ?_, ?_⟩
  · simpa only [AdjoinRoot.mk_X] using
      AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X_pow 2) (X_ne_zero (R := F)) (by simp)
  · rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

end TauCeti.Examples.Affinoid
