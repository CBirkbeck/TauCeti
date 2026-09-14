/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
-- supplies `UpperHalfPlane.forall_smul_eq_self_iff_mem_center`, which identifies the kernel
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

/-!
# The rational projective action on the upper half-plane

`GL(2, ℚ)⁺` does not act on `ℍ`; `PSL(2, ℝ)` does. This file supplies the homomorphism
between them, `ratPosToPSL2R`, and identifies its kernel on the determinant-one locus.

Hecke operators are indexed by double cosets of matrices with *rational* entries, so every
geometric statement about them has to be pushed along such a homomorphism before Mathlib's
`ℍ`-API applies. The change of scalars `GL(2, ℚ) →* GL(2, ℝ)` alone will not do: it is
injective, so it keeps `-1`, which acts trivially on `ℍ`. Anything demanding a *faithful*
action — `MeasureTheory.IsFundamentalDomain` in particular, whose a.e.-disjointness clause
is `Pairwise` over group elements — is then unsatisfiable. Passing to `PSL(2, ℝ)` collapses
exactly the scalars, and `eq_one_or_neg_one_of_mem_ker_of_det_eq_one` says that on the
determinant-one locus nothing else is lost: the kernel there is `{±1}`.

## Main definitions

* `Matrix.GeneralLinearGroup.map_mem_GLPos`: a strictly monotone ring hom carries `GLPos`
  to `GLPos`, so a change of scalars restricts to the positive-determinant subgroups.
* `TauCeti.ratPosToPSL2R`: the composite `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺ →* PSL(2, ℝ)`.

## Main results

* `TauCeti.ratPosToPSL2R_smul`: `ratPosToPSL2R g` acts on `ℍ` as the real matrix does.
* `TauCeti.eq_one_or_neg_one_of_mem_ker_of_det_eq_one`: an element of `ker ratPosToPSL2R`
  with determinant one is `±1`. Hence `ker ratPosToPSL2R ⊓ SL ≤ Γ` for any `Γ` containing
  `{±1}` — every `Γ₀(N)`, in particular.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.5
-/

public section

open Matrix UpperHalfPlane

open scoped MatrixGroups

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [DecidableEq n] [Fintype n] {R S : Type*}
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

/-- A strictly monotone change of scalars restricts to the positive-determinant subgroups:
the determinant commutes with the ring hom, and a strictly monotone ring hom is positive. -/
theorem map_mem_GLPos {f : R →+* S} (hf : StrictMono f) {g : GL n R} (hg : g ∈ GLPos n R) :
    g.map f ∈ GLPos n S := by
  have hdet : ((g.map f : GL n S) : Matrix n n S).det = f ((g : Matrix n n R).det) := by
    rw [val_map_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  refine (mem_glpos _).mpr ?_
  change 0 < ((g.map f : GL n S) : Matrix n n S).det
  rw [hdet, ← map_zero f]
  exact hf ((mem_glpos g).mp hg)

end Matrix.GeneralLinearGroup

namespace TauCeti

/-- The change of scalars `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺`, the restriction of
`Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)` to the positive-determinant subgroups. -/
noncomputable def ratPosToRealPos : GL(2, ℚ)⁺ →* GL(2, ℝ)⁺ :=
  ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)).comp (GLPos (Fin 2) ℚ).subtype).codRestrict _
    fun g ↦ Matrix.GeneralLinearGroup.map_mem_GLPos Rat.cast_strictMono g.2

/-- **The rational projective action.** `GL(2, ℚ)⁺` acts on `ℍ` through `PSL(2, ℝ)`. -/
noncomputable def ratPosToPSL2R : GL(2, ℚ)⁺ →* PSL(2, ℝ) :=
  glPosToPSL2R.comp ratPosToRealPos

/-- `ratPosToPSL2R g` acts on `ℍ` exactly as the real matrix `g` does. -/
theorem ratPosToPSL2R_smul (g : GL(2, ℚ)⁺) (τ : ℍ) :
    ratPosToPSL2R g • τ = Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) • τ :=
  glPosToPSL2R_smul (ratPosToRealPos g) τ

/-- An element of `ker ratPosToPSL2R` has central real image: it acts trivially on `ℍ`, and
`UpperHalfPlane.forall_smul_eq_self_iff_mem_center` says only the center does. -/
theorem map_mem_center_of_mem_ker {g : GL(2, ℚ)⁺} (hg : g ∈ ratPosToPSL2R.ker) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) ∈
      Subgroup.center (GL (Fin 2) ℝ) :=
  UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp fun τ ↦ by
    rw [← ratPosToPSL2R_smul g τ, MonoidHom.mem_ker.mp hg, one_smul]

/-- **The kernel meets the determinant-one locus in `{±1}`.** Central in `GL(2, ℝ)` means
scalar, a scalar of determinant one has scalar `±1`, and the change of scalars is injective. -/
theorem eq_one_or_neg_one_of_mem_ker_of_det_eq_one {g : GL(2, ℚ)⁺}
    (hg : g ∈ ratPosToPSL2R.ker) (hdet : ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1) :
    (g : GL (Fin 2) ℚ) = 1 ∨ (g : GL (Fin 2) ℚ) = -1 := by
  have hc := map_mem_center_of_mem_ker hg
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨c, hcs⟩ := hc
  have hdetR : ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.GeneralLinearGroup.val_map_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      hdet, map_one]
  have hc2 : c = 1 ∨ c = -1 := by
    have := congrArg (fun u : GL (Fin 2) ℝ ↦ (u : Matrix (Fin 2) (Fin 2) ℝ).det) hcs
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal] at this
    rw [hdetR] at this
    simpa [Fin.prod_univ_two] using this
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)) :=
    Matrix.GeneralLinearGroup.map_injective (algebraMap ℚ ℝ).injective
  rcases hc2 with h | h
  · refine Or.inl (hinj ?_)
    rw [← hcs, h]
    ext i j
    simp
  · refine Or.inr (hinj ?_)
    rw [← hcs, h]
    ext i j
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Units.val_neg, Units.val_one, Matrix.GeneralLinearGroup.val_map_apply, Matrix.map_apply,
      Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp

end TauCeti
