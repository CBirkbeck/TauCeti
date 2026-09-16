/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Basic

/-!
# Restricting a Hecke coset to a smaller ambient group

`HeckeCoset Δ Γ₁ Γ₂` records a double coset `Γ₁ δ Γ₂` inside an ambient group `G`. `HeckeCoset.map`
(`HeckeRing/Basic.lean`) moves along inclusions `Δ ≤ Δ'`, `Γ₁ ≤ Γ₁'`, `Γ₂ ≤ Γ₂'` *within a fixed*
`G`; nothing moves a Hecke coset between ambient groups, here or upstream — Mathlib's
`NumberTheory/HeckeRing/` holds only `Defs.lean`, which defines `HeckeCoset` and `mk` but no
transport. This file supplies the one direction that is
unobstructed: if the coefficient monoid already lies inside a subgroup `H`, the whole double coset
does, and `restrict` re-reads it as a Hecke coset over `↥H`.

## Why this is needed

A statement proved for an arbitrary ambient group is applied along a homomorphism `φ` out of that
group, and the available homomorphisms are frequently defined only on a *subgroup*. The motivating
case is `TauCeti.ratPosToPSL2R : GL(2, ℚ)⁺ →* PSL(2, ℝ)`: every homomorphism into a group acting
on `ℍ` starts from a positive-determinant or special-linear source, necessarily, since a
negative-determinant matrix carries `ℍ` to the lower half-plane. But the Hecke cosets of interest —
`HeckeRing.GL2.Delta0`, and the cosets built from it — live in `GL (Fin 2) ℚ`. Without `restrict`
there is no way to present one over `GL(2, ℚ)⁺`, and a theorem quantified over the ambient group
cannot be instantiated at `ratPosToPSL2R` at all.

## Main definitions

* `HeckeCoset.restrict`: re-reads `D : HeckeCoset Δ Γ₁ Γ₂` as a Hecke coset over `↥H`, for any
  subgroup `H` containing `Δ`.

## Main results

* `HeckeCoset.restrict_def`: the characteristic equation. `restrict` is not `@[expose]`, so a
  downstream module rewrites with this rather than unfolding the body.
* `HeckeCoset.restrict_injective`: `restrict` is injective — but not bijective, and the docstring
  there gives the counterexample.
* `HeckeCoset.mk_rep_restrict`: the representative chosen by the restricted coset is still a
  representative of `D`. Both `restrict D` and `D` pick their representatives through `Quotient.out`
  and there is no reason for the two choices to agree, so this — not an equation between
  representatives — is what a consumer needs.

## Implementation notes

Only `Δ ≤ H` is required. One might expect `Γ₁ ≤ H` and `Γ₂ ≤ H` as well, but `Subgroup.comap`
never asks the subgroup to sit inside `H`, and the proof of `mk_rep_restrict` needs only the easy
direction `a ∈ Γ₁.comap H.subtype → (a : G) ∈ Γ₁`, which is definitional.

Two spellings below look improvable and are not, both for the same reason — recording it here so it
is not rediscovered. `Γᵢ.comap H.subtype` is definitionally `Subgroup.subgroupOf`, which reads
better, but substituting it makes `restrict_def`'s `rfl` fail: `subgroupOf` is not `@[expose]`d, so
the equation cannot be proved definitionally in a module that exports it. The parentheses in
`:= (rfl)` are load-bearing for the same reason rather than stylistic; removing them produces the
identical export-transparency error. The same mismatch also defeats `simp`-family tactics here,
which normalise `comap H.subtype` to `subgroupOf` and then fail against a `comap`-shaped goal.
-/

public section

open Subgroup DoubleCoset

namespace HeckeCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} {Γ₁ Γ₂ H : Subgroup G}

/-- **Re-read a Hecke coset over a subgroup containing its coefficient monoid.** If `Δ ≤ H` then
every representative of `D` already lies in `H`, so the double coset `Γ₁ δ Γ₂` can be regarded as
one for the comapped triple inside `↥H`.

Only `Δ ≤ H` is needed; see the implementation notes in the module docstring. -/
noncomputable def restrict (hΔ : Δ ≤ H.toSubmonoid) (D : HeckeCoset Δ Γ₁ Γ₂) :
    HeckeCoset (Δ.comap H.subtype) (Γ₁.comap H.subtype) (Γ₂.comap H.subtype) :=
  mk _ _ ⟨⟨D.rep, hΔ D.rep.2⟩, D.rep.2⟩

/-- Defining equation for `restrict`. Since `restrict` is not `@[expose]`, a downstream module
rewrites with this instead of unfolding the body. -/
theorem restrict_def (hΔ : Δ ≤ H.toSubmonoid) (D : HeckeCoset Δ Γ₁ Γ₂) :
    restrict hΔ D = mk (Γ₁.comap H.subtype) (Γ₂.comap H.subtype)
      (⟨⟨D.rep, hΔ D.rep.2⟩, D.rep.2⟩ : ↥(Δ.comap H.subtype)) := (rfl)

/-- **The restricted coset's representative still represents `D`.** `restrict hΔ D` chooses its
representative through `Quotient.out`, independently of `D`'s own choice, so the two need not agree
as elements of `G`; what does hold — and what a consumer needs — is that the restricted choice is
again a representative of the original double coset. -/
theorem mk_rep_restrict (hΔ : Δ ≤ H.toSubmonoid) (D : HeckeCoset Δ Γ₁ Γ₂) :
    mk Γ₁ Γ₂ ⟨(restrict hΔ D).rep, (restrict hΔ D).rep.2⟩ = D := by
  -- the restricted representative lies in the double coset of the element `restrict` was built
  -- from, and the witnesses are comapped subgroup elements, hence genuine `Γᵢ`-elements downstairs
  obtain ⟨a, ha, b, hb, hab⟩ :=
    mem_doubleCoset.mp (restrict_def hΔ D ▸ rep_mk_mem_doubleCoset
      (⟨⟨D.rep, hΔ D.rep.2⟩, D.rep.2⟩ : ↥(Δ.comap H.subtype)))
  conv_rhs => rw [← mk_rep D]
  exact mk_eq_mk_of_mem (mem_doubleCoset.mpr ⟨(a : G), ha, (b : G), hb, congrArg Subtype.val hab⟩)

/-- **`restrict` is injective.** Immediate from `mk_rep_restrict`, which exhibits a left inverse.

It is *not* bijective at this generality, and no `Equiv` is available: taking `G = S₃`, `H = A₃`,
`Δ = H` and `Γ₁ = Γ₂ = {e, (1 2)}` gives a two-element `HeckeCoset Δ Γ₁ Γ₂` and a three-element
codomain. Surjectivity would need `Γ₁, Γ₂ ≤ H`, which nothing else here requires. -/
theorem restrict_injective (hΔ : Δ ≤ H.toSubmonoid) :
    Function.Injective (restrict hΔ : HeckeCoset Δ Γ₁ Γ₂ → _) :=
  fun D₁ D₂ h ↦ by rw [← mk_rep_restrict hΔ D₁, ← mk_rep_restrict hΔ D₂, h]

end HeckeCoset
