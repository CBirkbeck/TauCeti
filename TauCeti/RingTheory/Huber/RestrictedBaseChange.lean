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

* `baseChange` : the ambient comparison map `M ⊗[A] A⦃T₁, …, Tₖ⦄ →ₗ[A] M⦃T₁, …, Tₖ⦄`. It is
  Mathlib's `TensorProduct.piScalarRightHom` at the index type of `k`-variable power series.
* `restrictedSubringVal` : the inclusion `A⟨T₁, …, Tₖ⟩ → A⦃T₁, …, Tₖ⦄` as an `A`-linear map.
* `baseChangeRestricted` : the comparison map of Remark 8.29 itself,
  `M ⊗[A] A⟨T₁, …, Tₖ⟩ →ₗ[A] M⟨T₁, …, Tₖ⟩`.

## Main results

* `isRestricted_baseChange_tmul`: `baseChange` sends a pure tensor `m ⊗ₜ f` with `f` restricted
  to a restricted series. This is what makes the comparison land in `M⟨T₁, …, Tₖ⟩`, and it is
  where `ContinuousSMul A M` is used — continuity of `a ↦ a • m` in the *scalar*, which
  `ContinuousConstSMul` does not give.
* `isRestricted_baseChange`: `baseChange` carries the span of the restricted pure tensors into
  `M⟨T₁, …, Tₖ⟩`.
* `coe_baseChangeRestricted_tmul`: read in the ambient series, `baseChangeRestricted` agrees with
  `baseChange` on pure tensors.

The isomorphism itself — Remark 8.29 proper, which needs `M` finitely generated over a complete
strongly noetherian Tate ring — is not proved here.

## Implementation notes

`MvPowerSeries σ R` is a plain `def` for `(σ →₀ ℕ) → R`, so Mathlib's lemmas about
`TensorProduct.piScalarRightHom` are stated about a type that `rw` and `simp` will not unfold to
reach a goal phrased in power series. Two declarations answer this, and nothing else here crosses
the gap:

* `baseChange` ascribes the codomain of `TensorProduct.piScalarRightHom` as `M⦃T₁, …, Tₖ⦄`. The
  `simp` steps of the span induction in `isRestricted_baseChange` — `map_zero`, `map_add`,
  `map_smul` — match that ascription; against the unascribed `(Fin k →₀ ℕ) → M` form they rewrite
  to a term the goal no longer matches syntactically.
* the private `baseChange_tmul` restates Mathlib's `piScalarRightHom_tmul` at the series type;
  the results above reach the coefficients by rewriting with it.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Remark 8.29.
-/

public section

open Filter

namespace TauCeti.Huber

section Ambient

variable {k : ℕ} {A M : Type*} [CommSemiring A] [TopologicalSpace A] [AddCommMonoid M]
  [TopologicalSpace M] [Module A M]

/-- Mathlib's base-change map at the index type of `k`-variable power series, with its codomain
ascribed as `M⦃T₁, …, Tₖ⦄` rather than `(Fin k →₀ ℕ) → M`. It sends `m ⊗ₜ f` to
`s ↦ coeff s f • m`. -/
abbrev baseChange : TensorProduct A M (MvPowerSeries (Fin k) A) →ₗ[A] MvPowerSeries (Fin k) M :=
  TensorProduct.piScalarRightHom A A M (Fin k →₀ ℕ)

omit [TopologicalSpace A] [TopologicalSpace M] in
/-- `baseChange` sends a pure tensor `m ⊗ₜ f` to the coefficientwise scalar action
`s ↦ coeff s f • m`. -/
private theorem baseChange_tmul (m : M) (f : MvPowerSeries (Fin k) A) :
    baseChange (TensorProduct.tmul A m f)
      = show MvPowerSeries (Fin k) M from fun s ↦ MvPowerSeries.coeff s f • m :=
  -- Mathlib's `TensorProduct.piScalarRightHom_tmul` is this statement at the function type
  -- `(Fin k →₀ ℕ) → A`. `MvPowerSeries σ R` is a plain `def` for that type, so neither `rw` nor
  -- `simp` can match the lemma against a goal phrased in series: their matching runs at reducible
  -- transparency, which does not unfold it. A term-mode application does, at full transparency,
  -- so this is the one place the two phrasings are bridged; everything below rewrites with it.
  TensorProduct.piScalarRightHom_tmul A A M (Fin k →₀ ℕ) m f

/-- A pure tensor with restricted second factor base-changes to a restricted series.

The hypothesis is `ContinuousSMul A M`, not `ContinuousConstSMul A M`: the continuity needed is of
`a ↦ a • m` in the **scalar** variable, since it is the coefficients that vary and the vector that
is fixed. `ContinuousConstSMul` gives continuity in the vector variable instead. -/
theorem isRestricted_baseChange_tmul [ContinuousSMul A M] {f : MvPowerSeries (Fin k) A}
    (hf : IsRestricted f) (m : M) : IsRestricted (baseChange (TensorProduct.tmul A m f)) := by
  rw [baseChange_tmul]
  refine isRestricted_iff.mpr ?_
  have hc : Tendsto (fun a : A ↦ a • m) (nhds 0) (nhds ((0 : A) • m)) :=
    (continuous_id.smul continuous_const).tendsto 0
  rw [zero_smul] at hc
  exact hc.comp (isRestricted_iff_coeff.mp hf)

/-- Base change carries the span of the restricted pure tensors into `M⟨T₁, …, Tₖ⟩`.

The hypothesis is membership in that span rather than restrictedness of a chosen representative:
an element of a tensor product has many representations, and restrictedness of the image is not
visible from any single one. -/
theorem isRestricted_baseChange [ContinuousSMul A M] [ContinuousAdd M]
    {x : TensorProduct A M (MvPowerSeries (Fin k) A)}
    (hx : x ∈ Submodule.span A {t | ∃ (m : M) (f : MvPowerSeries (Fin k) A),
      IsRestricted f ∧ TensorProduct.tmul A m f = t}) :
    IsRestricted (baseChange x) := by
  induction hx using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨m, f, hf, rfl⟩ := ht
      exact isRestricted_baseChange_tmul hf m
  | zero => simp
  | add y z _ _ hy hz => simpa using hy.add hz
  | smul a y _ hy => simpa using hy.smul a

end Ambient

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

/-- **The comparison map of Wedhorn Remark 8.29**: `M ⊗[A] A⟨T₁, …, Tₖ⟩ →ₗ[A] M⟨T₁, …, Tₖ⟩`.

Mathlib's base-change map restricted on both sides. Remark 8.29 asserts that it is an isomorphism
when `M` is finitely generated over a complete strongly noetherian Tate ring, which is not proved
here. -/
noncomputable def baseChangeRestricted :
    TensorProduct A M (restrictedMvPowerSeriesSubring k A) →ₗ[A]
      restrictedMvPowerSeriesSubmodule k A M :=
  LinearMap.codRestrict _
    (baseChange.comp (TensorProduct.map LinearMap.id restrictedSubringVal))
    fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m f =>
          simpa using isRestricted_baseChange_tmul
            (mem_restrictedMvPowerSeriesSubring.mp f.2) m
      | add y z hy hz =>
          simpa using (mem_restrictedMvPowerSeriesSubmodule.mp hy).add
            (mem_restrictedMvPowerSeriesSubmodule.mp hz)

/-- Read in the ambient series, `baseChangeRestricted` is `baseChange` on the underlying series.
Compose with `baseChange_tmul` for the coefficients. -/
@[simp]
theorem coe_baseChangeRestricted_tmul (m : M) (f : restrictedMvPowerSeriesSubring k A) :
    ((baseChangeRestricted (TensorProduct.tmul A m f) :
        restrictedMvPowerSeriesSubmodule k A M) : MvPowerSeries (Fin k) M)
      = baseChange (TensorProduct.tmul A m (f : MvPowerSeries (Fin k) A)) := (rfl)

end Restricted

end TauCeti.Huber
