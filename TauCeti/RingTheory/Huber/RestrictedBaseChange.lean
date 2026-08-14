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
it exists: writing it down needs no finiteness and no completeness, only continuity of the scalar
action — beyond the nonarchimedean hypothesis that `A⟨T₁, …, Tₖ⟩` itself carries, without which
that subring is not defined.

The ambient map is Mathlib's: `TensorProduct.piScalarRightHom A A M (Fin k →₀ ℕ)` already has the
type `M ⊗[A] MvPowerSeries (Fin k) A →ₗ[A] MvPowerSeries (Fin k) M`.

## Main definitions

* `mvPowerSeriesBaseChange` : that map, with its codomain ascribed as `MvPowerSeries (Fin k) M`.
* `restrictedMvPowerSeriesSubringVal` : the inclusion `A⟨T₁, …, Tₖ⟩ → MvPowerSeries (Fin k) A` as
  an `A`-algebra map.
* `restrictedMvPowerSeriesBaseChange` : the comparison map of Remark 8.29 itself,
  `M ⊗[A] A⟨T₁, …, Tₖ⟩ →ₗ[A] M⟨T₁, …, Tₖ⟩`.

## Main results

* `mvPowerSeriesBaseChange_tmul`: the map sends `m ⊗ₜ f` to the coefficientwise scalar action
  `s ↦ coeff s f • m`. This is the only route to coefficients (see the implementation notes).
* `isRestricted_mvPowerSeriesBaseChange_tmul`: that series is restricted whenever `f` is. It is
  where `ContinuousSMul A M` is used — continuity of `a ↦ a • m` in the *scalar*, which
  `ContinuousConstSMul` does not give.
* `isRestricted_mvPowerSeriesBaseChange_map`: the same for an arbitrary element of
  `M ⊗[A] A⟨T₁, …, Tₖ⟩`.
* `coe_restrictedMvPowerSeriesBaseChange_tmul`: read in the ambient series, the restricted map
  agrees with the ambient one on pure tensors.

The isomorphism itself — Remark 8.29 proper, which needs `M` finitely generated over a complete
strongly noetherian Tate ring — is not proved here.

## Implementation notes

`MvPowerSeries σ R` is a plain `def` for `(σ →₀ ℕ) → R`, so Mathlib's lemmas about
`TensorProduct.piScalarRightHom` are stated about a type that `rw` and `simp` will not unfold to
reach a goal phrased in power series. Two declarations answer this, and nothing else here crosses
the gap:

* `mvPowerSeriesBaseChange` ascribes the codomain of `TensorProduct.piScalarRightHom` as
  `MvPowerSeries (Fin k) M`. The `simp` steps of the tensor induction in
  `isRestricted_mvPowerSeriesBaseChange_map` — `map_zero`, `map_add` — match that ascription;
  against the unascribed `(Fin k →₀ ℕ) → M` form they rewrite to a term the goal no longer matches
  syntactically.
* `mvPowerSeriesBaseChange_tmul` restates Mathlib's `piScalarRightHom_tmul` at the series type.
  It is public because it is the only characterisation of either map on a pure tensor: a
  coefficientwise form is not available, since `MvPowerSeries.coeff` needs `Semiring` on the
  coefficients and `M` is only an `AddCommMonoid`.

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
ascribed as `MvPowerSeries (Fin k) M` rather than `(Fin k →₀ ℕ) → M`. It sends `m ⊗ₜ f` to
`s ↦ coeff s f • m`. -/
abbrev mvPowerSeriesBaseChange :
    TensorProduct A M (MvPowerSeries (Fin k) A) →ₗ[A] MvPowerSeries (Fin k) M :=
  TensorProduct.piScalarRightHom A A M (Fin k →₀ ℕ)

omit [TopologicalSpace A] [TopologicalSpace M] in
/-- `mvPowerSeriesBaseChange` sends a pure tensor `m ⊗ₜ f` to the coefficientwise scalar action
`s ↦ coeff s f • m`. -/
theorem mvPowerSeriesBaseChange_tmul (m : M) (f : MvPowerSeries (Fin k) A) :
    mvPowerSeriesBaseChange (TensorProduct.tmul A m f)
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
theorem isRestricted_mvPowerSeriesBaseChange_tmul [ContinuousSMul A M] {f : MvPowerSeries (Fin k) A}
    (hf : IsRestricted f) (m : M) :
    IsRestricted (mvPowerSeriesBaseChange (TensorProduct.tmul A m f)) := by
  rw [mvPowerSeriesBaseChange_tmul]
  refine isRestricted_iff.mpr ?_
  have hc : Tendsto (fun a : A ↦ a • m) (nhds 0) (nhds ((0 : A) • m)) :=
    (continuous_id.smul continuous_const).tendsto 0
  rw [zero_smul] at hc
  exact hc.comp (isRestricted_iff_coeff.mp hf)

end Ambient

/-! ### Between the restricted objects -/

section Restricted

variable {k : ℕ} {A M : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousSMul A M] [ContinuousAdd M]

/-- The inclusion `A⟨T₁, …, Tₖ⟩ → MvPowerSeries (Fin k) A` as an `A`-algebra map. `A⟨T⟩` is a
`Subring` carrying an `Algebra A` instance rather than a `Subalgebra`, so `Subalgebra.val` does
not apply. -/
noncomputable def restrictedMvPowerSeriesSubringVal :
    restrictedMvPowerSeriesSubring k A →ₐ[A] MvPowerSeries (Fin k) A where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' a := by simp [coe_algebraMap_restrictedMvPowerSeriesSubring]

/-- `restrictedMvPowerSeriesSubringVal` is the underlying series. Its body is not exposed, so this
is how a consumer computes with it. -/
@[simp]
theorem restrictedMvPowerSeriesSubringVal_apply (f : restrictedMvPowerSeriesSubring k A) :
    restrictedMvPowerSeriesSubringVal f = (f : MvPowerSeries (Fin k) A) := (rfl)

/-- Base change of an element of `M ⊗[A] A⟨T₁, …, Tₖ⟩`, read in the ambient series, is
restricted. -/
theorem isRestricted_mvPowerSeriesBaseChange_map
    (x : TensorProduct A M (restrictedMvPowerSeriesSubring k A)) :
    IsRestricted (mvPowerSeriesBaseChange
      (TensorProduct.map LinearMap.id restrictedMvPowerSeriesSubringVal.toLinearMap x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
      simpa using isRestricted_mvPowerSeriesBaseChange_tmul
        (mem_restrictedMvPowerSeriesSubring.mp f.2) m
  | add y z hy hz => simpa using hy.add hz

/-- **The comparison map of Wedhorn Remark 8.29**: `M ⊗[A] A⟨T₁, …, Tₖ⟩ →ₗ[A] M⟨T₁, …, Tₖ⟩`.

Mathlib's base-change map restricted on both sides. Remark 8.29 asserts that it is an isomorphism
when `M` is finitely generated over a complete strongly noetherian Tate ring, which is not proved
here. -/
noncomputable def restrictedMvPowerSeriesBaseChange :
    TensorProduct A M (restrictedMvPowerSeriesSubring k A) →ₗ[A]
      restrictedMvPowerSeriesSubmodule k A M :=
  LinearMap.codRestrict _
    (mvPowerSeriesBaseChange.comp
      (TensorProduct.map LinearMap.id restrictedMvPowerSeriesSubringVal.toLinearMap))
    fun x ↦ mem_restrictedMvPowerSeriesSubmodule.mpr
      (isRestricted_mvPowerSeriesBaseChange_map x)

/-- Read in the ambient series, `restrictedMvPowerSeriesBaseChange` is `mvPowerSeriesBaseChange`
on the underlying series. Compose with `mvPowerSeriesBaseChange_tmul` for the coefficients. -/
@[simp]
theorem coe_restrictedMvPowerSeriesBaseChange_tmul (m : M)
    (f : restrictedMvPowerSeriesSubring k A) :
    ((restrictedMvPowerSeriesBaseChange (TensorProduct.tmul A m f) :
        restrictedMvPowerSeriesSubmodule k A M) : MvPowerSeries (Fin k) M)
      -- `codRestrict`, `LinearMap.comp` and `TensorProduct.map` on a pure tensor are all
      -- projections, and `restrictedMvPowerSeriesSubringVal` is `Subtype.val`.
      = mvPowerSeriesBaseChange (TensorProduct.tmul A m (f : MvPowerSeries (Fin k) A)) := (rfl)

end Restricted

end TauCeti.Huber

