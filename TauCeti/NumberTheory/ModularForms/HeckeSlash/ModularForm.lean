/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Cusps
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Form
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Holomorphic

/-!
# The slash sum descends to modular forms and to cusp forms

`Form.lean` bundles the double coset as an endomorphism of `SlashInvariantForm 𝒮ℒ k`, and flags
that this is *not* the roadmap's Layer 2(b) target because holomorphy and the cusp conditions are
not yet carried along. This file supplies exactly that: the two remaining structure fields.

Invariance comes from `heckeSlashEnd`, holomorphy from `mdifferentiable_heckeSlashSum`, and
boundedness at the cusps from `isBoundedAt_heckeSlashSum`; `coe_heckeSlashEnd` is what lets the
latter two, which are stated about the raw function `heckeSlashSum`, be read as statements about
the bundled form. The cusp-form case is then *derived* from the modular-form one, adding only
`zero_at_cusps'`, so neither invariance nor holomorphy is proved twice.

Both maps are also bundled as `Module.End ℂ`, which is the form Hecke operators are consumed in:
bundling is what lets them compose and later carry a ring structure.

The level here is `𝒮ℒ`, which carries mathlib's `Subgroup.IsArithmetic` instance — the hypothesis
the two cusp lemmas need. Descending further to `Γ₁(N)` is a separate step.

## Main definitions

* `HeckeRing.GL2.heckeSlashModularForm`: the double coset acting on `ModularForm 𝒮ℒ k`.
* `HeckeRing.GL2.heckeSlashCuspForm`: the same on `CuspForm 𝒮ℒ k`, which is the statement that
  **the action preserves cuspidality**.
* `HeckeRing.GL2.heckeSlashModularFormEnd`, `heckeSlashCuspFormEnd`: both bundled as
  `Module.End ℂ`.

## Main results

* `HeckeRing.GL2.coe_heckeSlashModularForm`, `coe_heckeSlashCuspForm`: both are `heckeSlashSum`
  on underlying functions.
* `HeckeRing.GL2.heckeSlashModularFormEnd_apply`, `heckeSlashCuspFormEnd_apply`: the bundled
  endomorphisms are the unbundled maps on elements.

## Provenance

Shape ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), lines 102-105:
`heckeT_p_cusp`, which assembles a `CuspForm` as `{ heckeT_p … with zero_at_cusps' := … }`. The
assembly is the same; the operator differs, since this repository's `heckeSlashSum` is the general
double-coset sum rather than `T_p`, and the level is `𝒮ℒ` rather than `Γ₁(N)`. AINTLIB's
`CuspForm.toModularForm'` (line 51) is not ported: mathlib already supplies the coercion, as the
`CoeTC` instance of `ModularFormClass` (`Mathlib/NumberTheory/ModularForms/Basic.lean`).

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- The structure projection of `heckeSlashEnd` is `heckeSlashSum`. `coe_heckeSlashEnd` states
this for the coercion `⇑`; the structure fields below are phrased with the projection `.toFun`
instead, and `heckeSlashEnd` being unexposed keeps the two from reducing into one another. This
bridge is what lets those fields be discharged by `rw` and `exact` rather than by an unrestricted
simp call. -/
private lemma toFun_heckeSlashEnd (f : SlashInvariantForm 𝒮ℒ k) :
    (heckeSlashEnd k D f).toFun = heckeSlashSum k D f :=
  coe_heckeSlashEnd k D f

/-- **The double coset acting on modular forms.** The underlying function is `heckeSlashSum`;
invariance is `heckeSlashEnd`, holomorphy is `mdifferentiable_heckeSlashSum`, and boundedness at
the cusps is `isBoundedAt_heckeSlashSum`. -/
noncomputable def heckeSlashModularForm (f : ModularForm 𝒮ℒ k) : ModularForm 𝒮ℒ k where
  toSlashInvariantForm := heckeSlashEnd k D f.toSlashInvariantForm
  holo' := by
    rw [coe_heckeSlashEnd]; exact mdifferentiable_heckeSlashSum k D f.holo'
  bdd_at_cusps' hc := by
    rw [toFun_heckeSlashEnd]
    exact isBoundedAt_heckeSlashSum k D (fun _ h ↦ f.bdd_at_cusps' h) hc

/-- The action is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashModularForm (f : ModularForm 𝒮ℒ k) :
    ⇑(heckeSlashModularForm k D f) = heckeSlashSum k D f :=
  coe_heckeSlashEnd k D f.toSlashInvariantForm

/-- The projection form of `coe_heckeSlashModularForm`, for the same reason as
`toFun_heckeSlashEnd`: the cusp-form field below is phrased with `.toFun`. -/
private lemma toFun_heckeSlashModularForm (f : ModularForm 𝒮ℒ k) :
    (heckeSlashModularForm k D f).toFun = heckeSlashSum k D f :=
  coe_heckeSlashModularForm k D f

/-- **The double coset acting on cusp forms** — the action preserves cuspidality. Only the
vanishing field is new: invariance and holomorphy are taken from `heckeSlashModularForm` at the
underlying modular form, so the two constructions are not proved twice. -/
noncomputable def heckeSlashCuspForm (f : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k :=
  { heckeSlashModularForm k D (f : ModularForm 𝒮ℒ k) with
    zero_at_cusps' := fun hc ↦ by
      rw [toFun_heckeSlashModularForm]
      exact isZeroAt_heckeSlashSum k D (fun _ h ↦ f.zero_at_cusps' h) hc }

/-- The action is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashCuspForm (f : CuspForm 𝒮ℒ k) :
    ⇑(heckeSlashCuspForm k D f) = heckeSlashSum k D f :=
  coe_heckeSlashModularForm k D (f : ModularForm 𝒮ℒ k)

/-- **The double coset as a `ℂ`-linear endomorphism of `ModularForm 𝒮ℒ k`.** This is the form
Hecke operators are consumed in: bundling is what lets them compose and later carry a ring
structure. -/
noncomputable def heckeSlashModularFormEnd : Module.End ℂ (ModularForm 𝒮ℒ k) where
  toFun := heckeSlashModularForm k D
  map_add' f g := by ext τ; simp [heckeSlashSum_add]
  map_smul' c f := by ext τ; simp [heckeSlashSum_smul]

/-- **The double coset as a `ℂ`-linear endomorphism of `CuspForm 𝒮ℒ k`.** -/
noncomputable def heckeSlashCuspFormEnd : Module.End ℂ (CuspForm 𝒮ℒ k) where
  toFun := heckeSlashCuspForm k D
  map_add' f g := by ext τ; simp [heckeSlashSum_add]
  map_smul' c f := by ext τ; simp [heckeSlashSum_smul]

/-- The endomorphism is `heckeSlashModularForm` on elements. -/
@[simp] lemma heckeSlashModularFormEnd_apply (f : ModularForm 𝒮ℒ k) :
    heckeSlashModularFormEnd k D f = heckeSlashModularForm k D f := (rfl)

/-- The endomorphism is `heckeSlashCuspForm` on elements. -/
@[simp] lemma heckeSlashCuspFormEnd_apply (f : CuspForm 𝒮ℒ k) :
    heckeSlashCuspFormEnd k D f = heckeSlashCuspForm k D f := (rfl)

end HeckeRing.GL2

end
