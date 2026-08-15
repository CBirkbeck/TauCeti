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

Both descents are the same three-line assembly. Invariance comes from `heckeSlashEnd`, holomorphy
from `mdifferentiable_heckeSlashSum`, and the cusp condition from `isBoundedAt_heckeSlashSum` or
`isZeroAt_heckeSlashSum`; `coe_heckeSlashEnd` is what lets the last two, which are stated about
the raw function `heckeSlashSum`, be read as statements about the bundled form.

The level here is `𝒮ℒ`, which carries mathlib's `Subgroup.IsArithmetic` instance — the hypothesis
the two cusp lemmas need. Descending further to `Γ₁(N)`, and bundling these maps as
`Module.End ℂ`, are separate steps.

## Main definitions

* `HeckeRing.GL2.heckeSlashModularForm`: the double coset acting on `ModularForm 𝒮ℒ k`.
* `HeckeRing.GL2.heckeSlashCuspForm`: the same on `CuspForm 𝒮ℒ k`, which is the statement that
  **the action preserves cuspidality**.

## Main results

* `HeckeRing.GL2.coe_heckeSlashModularForm`, `coe_heckeSlashCuspForm`: both are `heckeSlashSum`
  on underlying functions.

## Provenance

Shape ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), lines 102-105:
`heckeT_p_cusp`, which assembles a `CuspForm` as `{ heckeT_p … with zero_at_cusps' := … }`. The
assembly is the same; the operator differs, since this repository's `heckeSlashSum` is the general
double-coset sum rather than `T_p`, and the level is `𝒮ℒ` rather than `Γ₁(N)`. AINTLIB's
`CuspForm.toModularForm'` (line 51) is not ported: it duplicates mathlib's
`CuspForm.toModularFormₗ`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- **The double coset acting on modular forms.** The underlying function is `heckeSlashSum`;
invariance is `heckeSlashEnd`, holomorphy is `mdifferentiable_heckeSlashSum`, and boundedness at
the cusps is `isBoundedAt_heckeSlashSum`. -/
noncomputable def heckeSlashModularForm (f : ModularForm 𝒮ℒ k) : ModularForm 𝒮ℒ k where
  toSlashInvariantForm := heckeSlashEnd k D f.toSlashInvariantForm
  holo' := by
    simpa only [coe_heckeSlashEnd] using! mdifferentiable_heckeSlashSum k D f.holo'
  -- The cusp field needs the unrestricted simp set: `coe_heckeSlashEnd` alone rewrites the
  -- coercion but not the structure projection `.toFun`, which `heckeSlashEnd` being unexposed
  -- keeps opaque. The `!` is likewise load-bearing; plain `simpa` cannot cross that boundary.
  bdd_at_cusps' hc := by
    simpa using! isBoundedAt_heckeSlashSum k D (fun _ h ↦ f.bdd_at_cusps' h) hc

/-- **The double coset acting on cusp forms** — the action preserves cuspidality. -/
noncomputable def heckeSlashCuspForm (f : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k where
  toSlashInvariantForm := heckeSlashEnd k D f.toSlashInvariantForm
  holo' := by
    simpa only [coe_heckeSlashEnd] using! mdifferentiable_heckeSlashSum k D f.holo'
  zero_at_cusps' hc := by
    simpa using! isZeroAt_heckeSlashSum k D (fun _ h ↦ f.zero_at_cusps' h) hc

/-- The action is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashModularForm (f : ModularForm 𝒮ℒ k) :
    ⇑(heckeSlashModularForm k D f) = heckeSlashSum k D f :=
  coe_heckeSlashEnd k D f.toSlashInvariantForm

/-- The action is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashCuspForm (f : CuspForm 𝒮ℒ k) :
    ⇑(heckeSlashCuspForm k D f) = heckeSlashSum k D f :=
  coe_heckeSlashEnd k D f.toSlashInvariantForm

end HeckeRing.GL2

end
