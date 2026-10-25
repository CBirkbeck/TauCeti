/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.KoszulComplex.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Low-dimensional Koszul complexes

The Koszul complex of multiplication by one element has two terms, in degrees one and zero.
Its first homology is the annihilator of that element. This gives contrasting calculations for
multiplication by two over the integers and over `ZMod 4`, and for multiplication by zero over
the integers. The empty sequence gives a complex concentrated in degree zero.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.Examples.KoszulComplex
variable (R : Type*) [CommRing R]

/-- The one-element Koszul complex has no terms in degrees at least two. -/
theorem single_high_eq_zero (x : R) (n : ℕ)
    (v : (koszulComplex (LinearMap.mul R R x)).X (n + 2)) : v = 0 := by
  apply exteriorPower.eq_zero_of_finrank_lt
  simp only [CommSemiring.finrank_self]
  omega

/-- The Koszul complex of the empty sequence vanishes in every positive degree. -/
theorem empty_positive_eq_zero (n : ℕ)
    (v : (koszulComplex (Fintype.linearCombination R (fun i : Fin 0 => i.elim0))).X
    (n + 1)) : v = 0 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have hs : Subsingleton (⋀[R]^(n + 1) (Fin 0 → R)) := Module.subsingleton R _
    exact hs.elim v 0
  · apply exteriorPower.eq_zero_of_finrank_lt
    rw [Module.finrank_pi]
    simp

/-- The one-element Koszul complex has terms `R` in degrees zero and one, and its first
differential is multiplication by that element under the canonical exterior-power
identifications. -/
theorem single_low_degrees (x : R) :
    Nonempty ((koszulComplex (LinearMap.mul R R x)).X 0 ≃ₗ[R] R) ∧
    Nonempty ((koszulComplex (LinearMap.mul R R x)).X 1 ≃ₗ[R] R) ∧
    (∀ v, exteriorPower.zeroEquiv R R
      ((koszulComplex (LinearMap.mul R R x)).d 1 0 v) =
      x * exteriorPower.oneEquiv R R v) := by
  refine ⟨⟨exteriorPower.zeroEquiv R R⟩, ⟨exteriorPower.oneEquiv R R⟩, ?_⟩
  intro v
  rw [koszulComplex_d]
  exact zeroEquiv_koszulDifferential_zero (LinearMap.mul R R x) v

/-- The degree-zero term of the empty Koszul complex is the ground ring. -/
theorem empty_degree_zero : Nonempty
    ((koszulComplex (Fintype.linearCombination R (fun i : Fin 0 => i.elim0))).X 0 ≃ₗ[R] R) :=
  ⟨exteriorPower.zeroEquiv R (Fin 0 → R)⟩

private def homologyOneEquivKer (x : R) :
    (koszulComplex (LinearMap.mul R R x)).homology 1 ≃ₗ[R] LinearMap.ker (LinearMap.mul R R x) := by
  let C := koszulComplex (LinearMap.mul R R x)
  have hf : (C.sc' 2 1 0).f = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    have hv : v = 0 := exteriorPower.eq_zero_of_finrank_lt (R := R) (M := R) 2
      (by simp [CommSemiring.finrank_self]) v
    rw [hv]
    exact map_zero _
  let e := ((C.sc' 2 1 0).asIsoHomologyπ hf).symm ≪≫ (C.sc' 2 1 0).moduleCatCyclesIso
  let hC := C.homologyIsoSc' 2 1 0
    ((ComplexShape.down ℕ).prev_eq' (by rfl)) ((ComplexShape.down ℕ).next_eq' (by rfl))
  let eC : (koszulComplex (LinearMap.mul R R x)).homology 1 ≃ₗ[R]
      LinearMap.ker (koszulDifferential (LinearMap.mul R R x) 0) :=
    (hC ≪≫ e).toLinearEquiv
  let eK : LinearMap.ker (koszulDifferential (LinearMap.mul R R x) 0) ≃ₗ[R]
      LinearMap.ker (LinearMap.mul R R x) := by
    refine (exteriorPower.oneEquiv R R).ofSubmodules _ _ ?_
    ext r
    rw [Submodule.mem_map_equiv]
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      have he := congrArg (exteriorPower.zeroEquiv R R) h
      simpa [C, koszulComplex_d] using he
    · intro h
      apply (exteriorPower.zeroEquiv R R).injective
      simpa [C, koszulComplex_d] using h
  exact eC.trans eK

/-- Multiplication by two over the integers has zero first Koszul homology. -/
theorem int_two_homology_one : Subsingleton ((koszulComplex (LinearMap.mul ℤ ℤ 2)).homology 1) := by
  have hz (x : LinearMap.ker (LinearMap.mul ℤ ℤ 2)) : x = 0 := by
    apply Subtype.ext
    have h : 2 * (x : ℤ) = 0 := x.property
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  let : Subsingleton (LinearMap.ker (LinearMap.mul ℤ ℤ 2)) :=
    ⟨fun a b => (hz a).trans (hz b).symm⟩
  exact (homologyOneEquivKer ℤ 2).injective.subsingleton

/-- Multiplication by zero over the integers has first Koszul homology isomorphic to `ℤ`. -/
theorem int_zero_homology_one :
    Nonempty ((koszulComplex (LinearMap.mul ℤ ℤ 0)).homology 1 ≃ₗ[ℤ] ℤ) := by
  let e : LinearMap.ker (LinearMap.mul ℤ ℤ 0) ≃ₗ[ℤ] ℤ :=
    LinearEquiv.ofTop _ (by ext x; simp)
  exact ⟨(homologyOneEquivKer ℤ 0).trans e⟩

private def zmodTwoAddEquivKer : ZMod 2 ≃+ LinearMap.ker (LinearMap.mul (ZMod 4) (ZMod 4) 2) where
  toFun x := ⟨if x = 0 then 0 else 2, by fin_cases x <;> rfl⟩
  invFun x := if (x : ZMod 4) = 0 then 0 else 1
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by
    rcases x with ⟨x, hx⟩
    have h : (2 : ZMod 4) * x = 0 := hx
    apply Subtype.ext
    fin_cases x
    · rfl
    · exact False.elim ((by decide : (2 : ZMod 4) * 1 ≠ 0) h)
    · rfl
    · exact False.elim ((by decide : (2 : ZMod 4) * 3 ≠ 0) h)
  map_add' x y := by fin_cases x <;> fin_cases y <;> rfl

/-- Multiplication by two over `ZMod 4` has first Koszul homology isomorphic as an additive group
to `ZMod 2`; the zero divisor prevents positive-degree acyclicity. -/
theorem zmod_four_two_homology_one :
    Nonempty ((koszulComplex (LinearMap.mul (ZMod 4) (ZMod 4) 2)).homology 1 ≃+ ZMod 2) :=
  ⟨(homologyOneEquivKer (ZMod 4) 2).toAddEquiv.trans zmodTwoAddEquivKer.symm⟩

end TauCeti.Examples.KoszulComplex
