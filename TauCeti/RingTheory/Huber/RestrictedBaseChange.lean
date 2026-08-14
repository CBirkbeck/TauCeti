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
  rw [isRestricted_iff_apply]
  have hc : Tendsto (fun a : A ↦ a • m) (nhds 0) (nhds ((0 : A) • m)) :=
    (continuous_id.smul continuous_const).tendsto 0
  rw [zero_smul] at hc
  exact hc.comp (isRestricted_iff.mp hf)

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
      rw [map_smul, isRestricted_iff_apply]
      exact hc.comp (isRestricted_iff_apply.mp hy)

end TauCeti.Huber
