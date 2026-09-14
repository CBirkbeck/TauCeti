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
exactly the scalars, and `eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one` says that on the
determinant-one locus nothing else is lost: the kernel there is `{±1}`.

## Main definitions

* `TauCeti.ratPosToRealPos`: the change of scalars `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺`.
* `TauCeti.ratPosToPSL2R`: the composite `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺ →* PSL(2, ℝ)`.

## Main results

* `Matrix.GeneralLinearGroup.map_mem_glpos`: a strictly monotone ring hom carries `GLPos`
  to `GLPos`, so a change of scalars restricts to the positive-determinant subgroups.
* `TauCeti.ratPosToPSL2R_smul`: `ratPosToPSL2R g` acts on `ℍ` as the real matrix does.
* `TauCeti.eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one`: an element of
  `ker ratPosToPSL2R` with determinant one is `±1`. Hence `ker ratPosToPSL2R ⊓ SL ≤ Γ` for any
  `Γ` containing `{±1}` — every `Γ₀(N)`, in particular.

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

/-- A strictly monotone change of scalars restricts to the positive-determinant subgroups.

This is the side condition for cutting `Matrix.GeneralLinearGroup.map f` down to a homomorphism
`GLPos n R →* GLPos n S`; for `f = algebraMap ℚ ℝ` the hypothesis is `Rat.cast_strictMono`.
Contrast `Matrix.SpecialLinearGroup.toGLPos`, which lands in `GLPos` because the determinant
is `1`: here it is only positive, and monotonicity of `f` is what keeps it so. -/
theorem map_mem_glpos {f : R →+* S} (hf : StrictMono f) {g : GL n R} (hg : g ∈ GLPos n R) :
    g.map f ∈ GLPos n S := by
  -- the determinant commutes with the ring hom, and a strictly monotone ring hom is positive
  simpa [GeneralLinearGroup.map_det] using hf.lt_iff_lt.mpr hg

end Matrix.GeneralLinearGroup

namespace TauCeti

/-- The change of scalars `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺`, the restriction of
`Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)` to the positive-determinant subgroups. Its
underlying `GL (Fin 2) ℝ` matrix is that map applied to `g` definitionally, so a goal mixing
the two spellings closes by `rfl`. -/
noncomputable def ratPosToRealPos : GL(2, ℚ)⁺ →* GL(2, ℝ)⁺ :=
  (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)).restrict fun _ ↦
    Matrix.GeneralLinearGroup.map_mem_glpos Rat.cast_strictMono

/-- The underlying `GL (Fin 2) ℝ` matrix of `ratPosToRealPos g` is the change of scalars applied
to `g`. Definitionally true, but named so that goals mixing the two spellings close by
`rw`/`simp` rather than by unfolding — `ratPosToPSL2R_smul` currently relies on the defeq alone.
(`by rfl`, not `rfl`: `ratPosToRealPos` is not `@[expose]`, so a theorem exported from this
module cannot unfold it in term mode.) -/
theorem coe_ratPosToRealPos (g : GL(2, ℚ)⁺) :
    (ratPosToRealPos g : GL (Fin 2) ℝ) =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) := by rfl

/-- **The rational projective action.** `GL(2, ℚ)⁺` acts on `ℍ` through `PSL(2, ℝ)`: the change
of scalars `ratPosToRealPos` followed by the projectivization `glPosToPSL2R`. Compute the action
with `ratPosToPSL2R_smul`; unlike `ratPosToRealPos` this map is deliberately *not* injective, as
it collapses the scalar matrices, which act trivially on `ℍ`. -/
noncomputable def ratPosToPSL2R : GL(2, ℚ)⁺ →* PSL(2, ℝ) := glPosToPSL2R.comp ratPosToRealPos

/-- `ratPosToPSL2R g` acts on `ℍ` exactly as the real matrix `g` does. Rewriting with this
turns a goal about the `PSL(2, ℝ)`-action into one about Mathlib's `GL(2, ℝ)`-action on `ℍ`;
it is the `ℚ`-coefficient counterpart of `UpperHalfPlane.glPosToPSL2R_smul`. -/
theorem ratPosToPSL2R_smul (g : GL(2, ℚ)⁺) (τ : ℍ) :
    ratPosToPSL2R g • τ = Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) • τ :=
  glPosToPSL2R_smul (ratPosToRealPos g) τ

/-- An element of `ker ratPosToPSL2R` has central real image.

Central in `GL (Fin 2) ℝ` means scalar (`Matrix.GeneralLinearGroup.center_eq_range_scalar`), so
this alone pins the image down only up to a scalar; adding determinant one cuts it to `±1` —
that stronger form is `eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one`. -/
theorem map_mem_center_of_mem_ratPosToPSL2R_ker {g : GL(2, ℚ)⁺} (hg : g ∈ ratPosToPSL2R.ker) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) ∈ Subgroup.center
      (GL (Fin 2) ℝ) :=
  -- the real matrix acts on `ℍ` exactly as its projective class does, and that class is `1`
  UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp fun τ ↦ by
    rw [← ratPosToPSL2R_smul, MonoidHom.mem_ker.mp hg, one_smul]

/-- **The kernel meets the determinant-one locus in `{±1}`.**

Use it to discharge `ratPosToPSL2R.ker ⊓ H ≤ Γ` whenever `H` lies in the determinant-one locus
and `Γ` contains `{±1}` — every `Γ₀(N)`, in particular. Without `hdet` only
`map_mem_center_of_mem_ratPosToPSL2R_ker` is available, and that pins the image down to a
scalar, no further. -/
theorem eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one {g : GL(2, ℚ)⁺}
    (hg : g ∈ ratPosToPSL2R.ker)
    (hdet : ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1) :
    (g : GL (Fin 2) ℚ) = 1 ∨ (g : GL (Fin 2) ℚ) = -1 := by
  -- central in `GL(2, ℝ)` means scalar
  obtain ⟨c, hcs⟩ :=
    Matrix.GeneralLinearGroup.center_eq_range_scalar.le (map_mem_center_of_mem_ratPosToPSL2R_ker hg)
  -- a scalar of determinant one has scalar `±1`
  have hc2 : c = 1 ∨ c = -1 := by
    have hsq : (c : ℝ) ^ 2 = 1 := by
      simpa [Matrix.GeneralLinearGroup.map_det, hdet]
        using congrArg Units.val (congrArg Matrix.GeneralLinearGroup.det hcs)
    exact (sq_eq_one_iff.mp hsq).imp Units.ext Units.ext
  -- and the change of scalars is injective
  refine hc2.imp ?_ ?_ <;> rintro rfl <;>
    exact Matrix.GeneralLinearGroup.map_injective (algebraMap ℚ ℝ).injective <| by
      simpa [Units.ext_iff, ← RingHom.mapMatrix_apply, -Matrix.scalar_apply] using hcs.symm

end TauCeti
