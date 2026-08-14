/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.RestrictedPowerSeries
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Base change for restricted power series

Wedhorn's Remark 8.29 compares `M ⊗[A] A⟨T₁, …, Tₖ⟩` with `M⟨T₁, …, Tₖ⟩` for a finitely generated
module `M` over a complete Tate ring. This file builds the comparison map, in the generality where
it exists — no finiteness and no completeness are needed to *write* it down, only continuity of the
scalar action.

## Main definitions

* `coeffSmulSeries f m` : the series `s ↦ coeff s f • m`, the coefficientwise scalar action.
* `baseChange` : the comparison map `M ⊗[A] A⦃T₁, …, Tₖ⦄ →ₗ[A] M⦃T₁, …, Tₖ⦄`, characterised on
  pure tensors by `baseChange_tmul`.

## Main results

* `isRestricted_coeffSmulSeries`: `coeffSmulSeries f m` is restricted whenever `f` is. This is
  what makes the comparison land in `M⟨T₁, …, Tₖ⟩`, and it is where `ContinuousSMul A M` is used —
  continuity of `a ↦ a • m` in the *scalar*, which `ContinuousConstSMul` does not give.
* `isRestricted_baseChange`: `baseChange` carries the span of the restricted pure tensors into
  `M⟨T₁, …, Tₖ⟩`.

The isomorphism itself — Remark 8.29 proper, which needs `M` finitely generated over a complete
strongly noetherian Tate ring — is not proved here.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Remark 8.29.
-/

public section

open Filter

namespace TauCeti.Huber

variable {k : ℕ} {A M : Type*} [CommSemiring A] [TopologicalSpace A] [AddCommMonoid M]
  [TopologicalSpace M] [Module A M]

/-- The coefficientwise scalar action: the series whose `s`-th coefficient is `coeff s f • m`.

This is the value of the comparison map `M ⊗[A] A⟨T₁, …, Tₖ⟩ → M⟨T₁, …, Tₖ⟩` on a pure tensor
`m ⊗ₜ f`. -/
def coeffSmulSeries (f : MvPowerSeries (Fin k) A) (m : M) : MvPowerSeries (Fin k) M :=
  fun s : Fin k →₀ ℕ ↦ MvPowerSeries.coeff s f • m

omit [TopologicalSpace A] [TopologicalSpace M] in
/-- The coefficients of `coeffSmulSeries f m` are what the name says. The body is not exposed, so
this is how a consumer computes with it. -/
@[simp]
theorem coeffSmulSeries_apply (f : MvPowerSeries (Fin k) A) (m : M) (s : Fin k →₀ ℕ) :
    (coeffSmulSeries f m : (Fin k →₀ ℕ) → M) s = MvPowerSeries.coeff s f • m := (rfl)

/-- Scaling a restricted series coefficientwise by a fixed vector leaves it restricted.

The hypothesis is `ContinuousSMul A M` rather than `ContinuousConstSMul A M`: the continuity
needed is of `a ↦ a • m` in the **scalar** variable, and `ContinuousConstSMul` gives continuity of
`m ↦ a • m` in the vector variable instead. -/
theorem isRestricted_coeffSmulSeries [ContinuousSMul A M] {f : MvPowerSeries (Fin k) A}
    (hf : IsRestricted f) (m : M) : IsRestricted (coeffSmulSeries f m) := by
  refine (isRestricted_iff (f := coeffSmulSeries f m)).mpr ?_
  have hc : Tendsto (fun a : A ↦ a • m) (nhds 0) (nhds ((0 : A) • m)) :=
    (continuous_id.smul continuous_const).tendsto 0
  rw [zero_smul] at hc
  exact hc.comp (isRestricted_iff_coeff.mp hf)

/-- **The comparison map of Wedhorn Remark 8.29**, on the ambient power series:
`M ⊗[A] A⦃T₁, …, Tₖ⦄ → M⦃T₁, …, Tₖ⦄`, sending `m ⊗ₜ f` to `s ↦ coeff s f • m`.

Remark 8.29 asserts that this restricts to an isomorphism `M ⊗[A] A⟨T⟩ ≅ M⟨T⟩` for finitely
generated `M`; that it is *defined* needs neither finiteness nor a topology, so it is built here
in the algebraic generality it has, and `isRestricted_coeffSmulSeries` is what carries it to the
restricted objects. -/
noncomputable def baseChange :
    TensorProduct A M (MvPowerSeries (Fin k) A) →ₗ[A] MvPowerSeries (Fin k) M :=
  TensorProduct.lift <| LinearMap.mk₂ A (fun (m : M) (f : MvPowerSeries (Fin k) A) ↦
      coeffSmulSeries f m)
    (fun m₁ m₂ f ↦ funext fun s ↦ smul_add _ m₁ m₂)
    (fun a m f ↦ funext fun s ↦ smul_comm _ a m)
    (fun m f₁ f₂ ↦ funext fun s ↦ by
      change MvPowerSeries.coeff s (f₁ + f₂) • m
        = MvPowerSeries.coeff s f₁ • m + MvPowerSeries.coeff s f₂ • m
      rw [map_add, add_smul])
    (fun a m f ↦ funext fun s ↦ by
      change MvPowerSeries.coeff s (a • f) • m = a • (MvPowerSeries.coeff s f • m)
      rw [map_smul, smul_eq_mul, mul_smul])

omit [TopologicalSpace A] [TopologicalSpace M] in
@[simp]
theorem baseChange_tmul (m : M) (f : MvPowerSeries (Fin k) A) :
    baseChange (TensorProduct.tmul A m f) = coeffSmulSeries f m := (rfl)

/-- The comparison map carries `M ⊗[A] A⟨T₁, …, Tₖ⟩` into `M⟨T₁, …, Tₖ⟩`.

The hypothesis is membership in the span of the *restricted* pure tensors rather than
`IsRestricted`-ness of a chosen representative: an element of the tensor product has many
representations, and restrictedness of the image is not visible from any one of them. Proved by
induction over that span, which is why `ContinuousAdd M` appears — the additive step needs sums of
null sequences to be null. -/
theorem isRestricted_baseChange [ContinuousSMul A M] [ContinuousAdd M]
    (x : TensorProduct A M (MvPowerSeries (Fin k) A))
    (hx : x ∈ Submodule.span A {t | ∃ (m : M) (f : MvPowerSeries (Fin k) A),
      IsRestricted f ∧ TensorProduct.tmul A m f = t}) :
    IsRestricted (baseChange x) := by
  induction hx using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨m, f, hf, rfl⟩ := ht
      simpa using isRestricted_coeffSmulSeries hf m
  | zero => simp
  | add y z _ _ hy hz => simpa using hy.add hz
  | smul a y _ hy =>
      have hc : Tendsto (fun v : M ↦ a • v) (nhds 0) (nhds (a • (0 : M))) :=
        (continuous_const_smul a).tendsto 0
      rw [smul_zero] at hc
      rw [map_smul]
      exact (isRestricted_iff (f := a • baseChange y)).mpr
        (hc.comp ((isRestricted_iff (f := baseChange y)).mp hy))

/-! ### Between the restricted objects -/

section Restricted

variable {k : ℕ} {A M : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousSMul A M] [ContinuousAdd M]

/-- The inclusion `A⟨T₁, …, Tₖ⟩ → A⦃T₁, …, Tₖ⦄` as an `A`-linear map. `A⟨T⟩` is a `Subring`
rather than a `Subalgebra`, so there is no `val` to reuse. -/
noncomputable def restrictedSubringVal :
    restrictedMvPowerSeriesSubring k A →ₗ[A] MvPowerSeries (Fin k) A where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' a x := by
    simp only [Algebra.smul_def, Subring.coe_mul, RingHom.id_apply,
      coe_algebraMap_restrictedMvPowerSeriesSubring]

/-- `restrictedSubringVal` is the underlying series. Its body is not exposed, so this is how a
consumer computes with it. -/
@[simp]
theorem restrictedSubringVal_apply (f : restrictedMvPowerSeriesSubring k A) :
    restrictedSubringVal f = (f : MvPowerSeries (Fin k) A) := (rfl)

/-- **The comparison map of Wedhorn Remark 8.29**, between the objects the remark names:
`M ⊗[A] A⟨T₁, …, Tₖ⟩ →ₗ[A] M⟨T₁, …, Tₖ⟩`.

This is `baseChange` restricted on both sides, so it inherits that map's linearity rather than
re-proving it; `isRestricted_coeffSmulSeries` is what lets the codomain be cut down. Remark 8.29
asserts that this is an isomorphism when `M` is finitely generated over a complete strongly
noetherian Tate ring, which is not proved here. -/
noncomputable def baseChangeRestricted :
    TensorProduct A M (restrictedMvPowerSeriesSubring k A) →ₗ[A]
      restrictedMvPowerSeriesSubmodule k A M :=
  LinearMap.codRestrict _ (baseChange.comp (TensorProduct.map LinearMap.id restrictedSubringVal))
    fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero =>
          simp only [map_zero]
          exact mem_restrictedMvPowerSeriesSubmodule.mpr (isRestricted_zero k M)
      | tmul m f =>
          simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
            restrictedSubringVal_apply, baseChange_tmul]
          exact mem_restrictedMvPowerSeriesSubmodule.mpr
            (isRestricted_coeffSmulSeries (mem_restrictedMvPowerSeriesSubring.mp f.2) m)
      | add y z hy hz =>
          simp only [map_add]
          exact mem_restrictedMvPowerSeriesSubmodule.mpr
            ((mem_restrictedMvPowerSeriesSubmodule.mp hy).add
              (mem_restrictedMvPowerSeriesSubmodule.mp hz))

@[simp]
theorem coe_baseChangeRestricted_tmul (m : M) (f : restrictedMvPowerSeriesSubring k A) :
    ((baseChangeRestricted (TensorProduct.tmul A m f) :
        restrictedMvPowerSeriesSubmodule k A M) : MvPowerSeries (Fin k) M)
      = coeffSmulSeries (f : MvPowerSeries (Fin k) A) m := (rfl)

end Restricted

end TauCeti.Huber
