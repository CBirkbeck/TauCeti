/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus

/-!
# The twisted slash sum on the `Γ₀(N)` Hecke ring, and the nebentypus function space

`HeckeSlash/Nebentypus.lean` attaches to each double coset `D` of `Γ₀(N)` the nebentypus-twisted
slash sum, bundled as `twistedHeckeSlashSumEnd k χ D : Module.End ℂ (ℍ → ℂ)`. This file does two
things with it, both preparatory to the ring action on `M_k(Γ₁(N), χ)` of Layer 2(b).

First, it extends the assignment `D ↦ twistedHeckeSlashSumEnd k χ D` `ℤ`-linearly over the basis
of the Hecke ring `𝕋 Δ₀(N) Γ₀(N) ℤ`, exactly as `HeckeSlash/Ring.lean` extends the unweighted
`Γ₁(N)` operators: the extension is `Finsupp.linearCombination` at the coefficient ring `ℤ`, so
linearity in the ring element is inherited rather than reproved, and the one lemma stated is the
value on a basis element. As there, this is **not** a ring action — multiplicativity is Shimura
§3.4 and is not proved here — and it assigns endomorphisms of *all* functions `ℍ → ℂ`, not of a
character space.

Second, it names the space those endomorphisms are meant to act on: the `ℂ`-submodule of
functions `ℍ → ℂ` satisfying the nebentypus relation `f ∣[k] γ = χ(d_γ) • f` for every
`γ ∈ Γ₀(N)`. The relation is verbatim the right-hand side of
`mem_modFormCharSpace_iff_nebentypus`, and `coe_mem_nebentypusFunctionSpace_iff` records that a
modular form for `Γ₁(N)` lies in it exactly when it lies in `modFormCharSpace k χ`.

⚠ That the extended operators preserve `nebentypusFunctionSpace k χ` — the pay-off of the
weighting, and what makes the space the right codomain — is **not** proved here. It is the
twisted form of Shimura's Proposition 3.37 and is the next step, not this one; no statement
below mentions the two constructions together.

## Main definitions

* `HeckeRing.GL2.twistedHeckeSlashRingLinearMap`: the `ℤ`-linear extension of
  `twistedHeckeSlashSumEnd` to the Hecke ring `𝕋 Δ₀(N) Γ₀(N) ℤ`.
* `HeckeRing.GL2.nebentypusFunctionSpace`: the `ℂ`-submodule of `ℍ → ℂ` of functions with
  nebentypus `χ` under `Γ₀(N)`.

## Main results

* `HeckeRing.GL2.twistedHeckeSlashRingLinearMap_single`: the value on a basis element is the
  scaled twisted operator of that double coset. With `map_zero`/`map_add` this determines the
  map, so no further computation rules are restated.
* `HeckeRing.GL2.mem_nebentypusFunctionSpace_iff`,
  `HeckeRing.GL2.coe_mem_nebentypusFunctionSpace_iff`: membership is the nebentypus relation,
  and on modular forms for `Γ₁(N)` it is membership in `modFormCharSpace k χ`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck),
[`HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`](https://github.com/CBirkbeck/AINTLIB) at
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, lines 203–243: declarations
`twistedHeckeSlashExtGen`, `twistedHeckeSlashExtGen_add`, `IsGamma0TwistedInvariant` and
`gamma0TwistedInvariantFunctionSubmodule`. The source writes the extension out as a
`Finsupp.sum` and proves its additivity by hand; here it is `Finsupp.linearCombination`, so
additivity is `map_add` and is not restated. The source's standalone invariance predicate is
not ported: `main` already states that relation as the right-hand side of
`mem_modFormCharSpace_iff_nebentypus`, so the submodule's carrier is that relation directly and
the bridge to the character space is proved rather than left implicit. The source quantifies
its relation over the rational Hecke-pair subgroup and evaluates the character on an adjugate;
here it quantifies over `Γ₀(N) ≤ SL(2, ℤ)` and reads the character through `Gamma0Map`, which
is the form the character space on `main` uses.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4–3.5.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

public section

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

section Ring

variable [NeZero N]

/-- The `ℤ`-linear extension of `twistedHeckeSlashSumEnd` to formal `ℤ`-combinations of double
cosets of `Γ₀(N)`: `ℤ`-linear in the ring element, but not known to be multiplicative, so this is
not yet a ring action; and valued in endomorphisms of all of `ℍ → ℂ`, not of a character space.

`𝕋 Δ H ℤ` unfolds to `HeckeCoset Δ H H →₀ ℤ` carrying the transported module structure, which
is why `Finsupp.linearCombination` applies at this type: the ascription below crosses the
`HeckeCosetModule` wrapper. -/
noncomputable def twistedHeckeSlashRingLinearMap :
    𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ →ₗ[ℤ] Module.End ℂ (ℍ → ℂ) :=
  -- Not eta-reduced: `twistedHeckeSlashSumEnd` binds its `[NeZero N]` instance after `D`, so
  -- `twistedHeckeSlashSumEnd k χ` is not a function `HeckeCoset … → Module.End ℂ (ℍ → ℂ)`.
  Finsupp.linearCombination ℤ fun D ↦ twistedHeckeSlashSumEnd k χ D

/-- The value on a basis element is the scaled twisted operator of that double coset. -/
@[simp] lemma twistedHeckeSlashRingLinearMap_single
    (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))) (c : ℤ) :
    twistedHeckeSlashRingLinearMap k χ (HeckeCosetModule.single ℤ D c) =
      c • twistedHeckeSlashSumEnd k χ D :=
  -- `Finsupp.linearCombination_single` does not apply: `HeckeCosetModule.single` is a separate,
  -- non-exposed `def`, so that lemma's left-hand side does not match. The step to the
  -- `Finsupp.sum` shape is `Finsupp.linearCombination_apply`, and
  -- `HeckeCosetModule.sum_single_index` is the wrapper that exists for what follows.
  (Finsupp.linearCombination_apply (R := ℤ) (v := fun D ↦ twistedHeckeSlashSumEnd k χ D) _).trans
    (HeckeCosetModule.sum_single_index ℤ (zero_smul _ _))

end Ring

section Space

/-- **The nebentypus function space**: the functions `f : ℍ → ℂ` with `f ∣[k] γ = χ(d_γ) • f`
for every `γ ∈ Γ₀(N)`, where `d_γ` is the lower-right entry read through `Gamma0Map`. This is
the relation by which `mem_modFormCharSpace_iff_nebentypus` characterises `M_k(Γ₁(N), χ)`,
taken on arbitrary functions rather than on modular forms; the two agree on modular forms
(`coe_mem_nebentypusFunctionSpace_iff`). Closure under scalars uses that `Γ₀(N)` acts through
`SL(2, ℤ)`, whose slash commutes with complex scalars. -/
noncomputable def nebentypusFunctionSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | ∀ g : ↥(Gamma0 N),
    f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ ((Gamma0Map N).toHomUnits g)) : ℂ) • f}
  zero_mem' := by
    intro g
    rw [SlashAction.zero_slash, smul_zero]
  add_mem' hf hg := by
    intro g
    rw [SlashAction.add_slash, hf g, hg g, smul_add]
  smul_mem' c f hf := by
    intro g
    change (c • f) ∣[k] (g : SL(2, ℤ)) = _
    rw [ModularForm.SL_smul_slash, show f ∣[k] (g : SL(2, ℤ)) = _ from hf g, smul_comm]

/-- Membership in the nebentypus function space is the nebentypus relation. -/
@[simp] lemma mem_nebentypusFunctionSpace_iff {f : ℍ → ℂ} :
    f ∈ nebentypusFunctionSpace k χ ↔ ∀ g : ↥(Gamma0 N),
      f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ ((Gamma0Map N).toHomUnits g)) : ℂ) • f :=
  Iff.rfl

/-- **Bridge**: a modular form for `Γ₁(N)` lies in the nebentypus function space exactly when it
lies in the character space `modFormCharSpace k χ`. -/
lemma coe_mem_nebentypusFunctionSpace_iff (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∈ nebentypusFunctionSpace k χ ↔ f ∈ modFormCharSpace k χ := by
  rw [mem_nebentypusFunctionSpace_iff, mem_modFormCharSpace_iff_nebentypus]

end Space

end

end HeckeRing.GL2
