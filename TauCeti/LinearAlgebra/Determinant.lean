/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Determinant

public section

/-!
# Determinant transformation laws

Precomposing an alternating form of top degree with an endomorphism `φ` multiplies it by
`LinearMap.det φ`, and — the direction that is actually used — a form which is merely known to be
*scaled* by some `d` thereby identifies `d` as the determinant, without computing it. This file
records that law in three vocabularies: for an `AlternatingMap` indexed by a basis' index type,
for an alternating bilinear form on a rank-two module, and for the standard-basis determinant form
under matrix multiplication.

Mathlib's `Module.Basis.det_comp` is the case `ω = b.det` of the first statement. The step taken
here is that every top-degree alternating form is a multiple of `b.det`
(`AlternatingMap.eq_smulRight_basis_det`), so the same law holds for all of them; that is what
makes the converse available for a form supplied by something other than a basis, such as a
pairing.

## Main results

* `AlternatingMap.eq_smulRight_basis_det`: `ω = b.det.smulRight (ω b)` for `ω` of top degree.
* `AlternatingMap.compLinearMap_eq_det_smul`: `ω ∘ φ = det φ • ω` for `ω` of top degree.
* `LinearMap.det_eq_of_compLinearMap_eq_smul`: if `ω ≠ 0` and `ω ∘ φ = d • ω` then `det φ = d`.
* `LinearMap.IsAlt.compl₁₂_self_eq_det_smul` and `LinearMap.det_eq_of_compl₁₂_self_eq_smul`: the
  same two statements for an alternating bilinear form on a module of rank two.
* `TauCeti.Matrix.detRowAlternating_mulVec`: multiplication by a square matrix scales the
  standard-basis determinant form by the matrix determinant.

## Implementation notes

The forms are valued in an arbitrary module `N`, not in `R`. Mathlib's
`AlternatingMap.eq_smul_basis_det` and `AlternatingMap.map_basis_ne_zero_iff` are the `N = R` case
of the first result here and of a step inside the recovery proofs; the codomain plays no part in
either argument, only the coordinates do, so the `N`-valued statements are what is proved.

The recovery statements need a cancellation hypothesis, not just `ω ≠ 0`: over `ZMod 4`, with
`N = R`, the form `ω = 2 • b.det` is nonzero and satisfies `ω ∘ id = 3 • ω`, while `det id = 1`.
`NoZeroSMulDivisors R N` is assumed for them, and for nothing else; for `N = R` it is implied by
`NoZeroDivisors R`.

None of the transformation laws is a `simp` lemma: the basis they are proved from does not occur
in the statement, so `simp` could not infer it.

The bilinear statements go through a private reading of an alternating bilinear form as an
`AlternatingMap` on `Fin 2`. That conversion is deliberately not exported. The converse direction
already exists, as `TauCeti.MultilinearMap.toBilinForm`, and an exported version of this one
should be the matching half of that correspondence — over a `CommSemiring`, with the round trips —
rather than the one-way, proof-indexed constructor needed here.
-/

open Module

namespace AlternatingMap

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **A top-degree alternating form is its basis determinant times its value on the basis.** This
is Mathlib's `AlternatingMap.eq_smul_basis_det` with the codomain no longer required to be `R`:
the argument reads off the coordinates and never touches the values. -/
theorem eq_smulRight_basis_det [Fintype ι] [DecidableEq ι] (b : Basis ι R M)
    (ω : M [⋀^ι]→ₗ[R] N) : ω = b.det.smulRight (ω ⇑b) := by
  refine Module.Basis.ext_alternating b fun i h => ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  change ω (⇑b ∘ σ) = (b.det.smulRight (ω ⇑b)) (⇑b ∘ σ)
  simp [map_perm, Basis.det_self]

/-- **An endomorphism scales a top-degree alternating form by its determinant.** Here `ω` is of
top degree in the sense that its index type indexes a basis of `M`; the basis itself does not
occur in the statement. -/
theorem compLinearMap_eq_det_smul [Finite ι] (b : Basis ι R M) (ω : M [⋀^ι]→ₗ[R] N)
    (φ : M →ₗ[R] M) : ω.compLinearMap φ = LinearMap.det φ • ω := by
  cases nonempty_fintype ι
  classical
  ext v
  rw [compLinearMap_apply, eq_smulRight_basis_det b ω]
  simp only [smulRight_apply, smul_apply]
  rw [← Function.comp_def, Basis.det_comp, mul_smul]

end AlternatingMap

namespace LinearMap

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **The multiplier of a nonzero top-degree alternating form is the determinant.** An
endomorphism which scales `ω` by `d` has `det φ = d`; the scaling identifies the determinant
without computing it, and only the one endomorphism is involved. -/
theorem det_eq_of_compLinearMap_eq_smul [Finite ι] [NoZeroSMulDivisors R N] (b : Basis ι R M)
    {ω : M [⋀^ι]→ₗ[R] N} (hω : ω ≠ 0) {φ : M →ₗ[R] M} {d : R}
    (h : ω.compLinearMap φ = d • ω) : LinearMap.det φ = d := by
  cases nonempty_fintype ι
  classical
  have hb : ω ⇑b ≠ 0 := fun h0 =>
    hω (by rw [AlternatingMap.eq_smulRight_basis_det b ω, h0]; ext v; simp)
  rw [AlternatingMap.compLinearMap_eq_det_smul b ω φ] at h
  have h2 := congrArg (fun f : M [⋀^ι]→ₗ[R] N => f ⇑b) h
  simp only [AlternatingMap.smul_apply] at h2
  have h3 : (LinearMap.det φ - d) • ω ⇑b = 0 := by rw [sub_smul, h2, sub_self]
  exact sub_eq_zero.mp
    ((NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero h3).resolve_right hb)

section RankTwo

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An alternating bilinear form read as an alternating map in two arguments. -/
private def IsAlt.toAlternatingMap {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt) :
    M [⋀^Fin 2]→ₗ[R] N where
  toFun v := ω (v 0) (v 1)
  map_update_add' v i x y := by fin_cases i <;> simp
  map_update_smul' v i c x := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all [LinearMap.IsAlt.self_eq_zero halt]

@[simp]
private theorem IsAlt.toAlternatingMap_apply {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt)
    (v : Fin 2 → M) : halt.toAlternatingMap v = ω (v 0) (v 1) := rfl

private theorem IsAlt.toAlternatingMap_ne_zero {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt)
    (hω : ω ≠ 0) : halt.toAlternatingMap ≠ 0 := by
  contrapose! hω
  ext x y
  exact congrArg (fun f : M [⋀^Fin 2]→ₗ[R] N => f ![x, y]) hω

/-- **An endomorphism of a rank-two module scales an alternating bilinear form by its
determinant.** The basis witnesses that the rank is two and does not occur in the statement. -/
theorem IsAlt.compl₁₂_self_eq_det_smul (b : Basis (Fin 2) R M) {ω : M →ₗ[R] M →ₗ[R] N}
    (halt : ω.IsAlt) (φ : M →ₗ[R] M) : ω.compl₁₂ φ φ = LinearMap.det φ • ω := by
  ext x y
  have h := AlternatingMap.compLinearMap_eq_det_smul b halt.toAlternatingMap φ
  simpa using congrArg (fun f : M [⋀^Fin 2]→ₗ[R] N => f ![x, y]) h

/-- **The multiplier of a nonzero alternating bilinear form on a rank-two module is the
determinant.** This is the form the additivised Weil pairing supplies: its scaling by an isogeny's
degree identifies that degree as a determinant. -/
theorem det_eq_of_compl₁₂_self_eq_smul [NoZeroSMulDivisors R N] (b : Basis (Fin 2) R M)
    {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt) (hω : ω ≠ 0) {φ : M →ₗ[R] M} {d : R}
    (h : ω.compl₁₂ φ φ = d • ω) : LinearMap.det φ = d := by
  refine det_eq_of_compLinearMap_eq_smul b (halt.toAlternatingMap_ne_zero hω) ?_
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  simpa using DFunLike.congr_fun (DFunLike.congr_fun h (v 0)) (v 1)

end RankTwo

end LinearMap

namespace TauCeti

open Matrix

universe u

variable (k : Type u)

namespace Matrix

/-- Multiplication by a square matrix scales the standard-basis determinant form by its
determinant.

This is `AlternatingMap.compLinearMap_eq_det_smul` at `ω = (Pi.basisFun k ι).det`, but it is
proved from `Module.Basis.det_comp` instead: that lands directly in the matrix vocabulary its
`simp`-normal form needs, where the general law would have to be transported into it. -/
@[simp]
theorem detRowAlternating_mulVec [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) (v : ι → ι → k) :
    Matrix.detRowAlternating (fun i => M *ᵥ v i) =
      M.det * Matrix.detRowAlternating v := by
  simpa only [Pi.basisFun_det, Function.comp_def, Matrix.toLin'_apply, Matrix.mulVecBilin_apply,
    LinearMap.det_toLin'] using
    (Module.Basis.det_comp (Pi.basisFun k ι) (Matrix.toLin' M) v)

end Matrix

end TauCeti
