/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Unit
public import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# The addition series presented over `Fin 2`

`formalAdd` is indexed by `Unit ⊕ Unit`, one variable per chord parameter, which is the shape every
series-level lemma about it is stated in. Mathlib's `FormalGroup`, by contrast, carries a power
series in `MvPowerSeries (Fin 2) R`. This file transports exactly those facts a `FormalGroup` asks
for along the reindexing `sumUnitEmbFinTwo`, which carries no elliptic content and so lives
with the `MvPowerSeries` API, in `TauCeti.RingTheory.MvPowerSeries.Rename`.

`formalAdd` over `Unit ⊕ Unit` stays the working object: nothing here re-founds it over `Fin 2`,
and the `Fin 2` presentation is not intended as a second public spelling of the addition series.
It exists to be the `toPowerSeries` field of the `FormalGroup` instance, and the lemmas below are
its structure fields.

## Main results

* `WeierstrassCurve.constantCoeff_renameFin_formalAdd`, `.coeff_single_zero_renameFin_formalAdd`,
  `.coeff_single_one_renameFin_formalAdd`: the three coefficient conditions.
* `WeierstrassCurve.subst_renameFin_formalAdd`: substituting into the reindexed series, which is
  what carries an identity stated over `Unit ⊕ Unit` to one over `Fin 2`.

## Provenance

No external source. Michael Stoll's development states the group law over `Unit`-indexed sums
throughout and bundles it into his own `FormalGroupLaw` structure, so the reindexing has no
counterpart there; it is the cost of refounding on Mathlib's `FormalGroup`, whose `assoc` field is
stated over `Fin 2`.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries Filter Finsupp

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The reindexed addition series vanishes at the origin — the `zero_constantCoeff` field.

Deliberately not `@[simp]`: `simp` already discharges this from
`MvPowerSeries.constantCoeff_rename` and `constantCoeff_formalAdd`, both of which are
themselves `@[simp]`, so tagging it would add a rewrite duplicating an existing one. It is
named because it is a structure field of the eventual `FormalGroup` instance, not because a
caller needs it as a rewrite rule. -/
theorem constantCoeff_renameFin_formalAdd :
    constantCoeff (rename sumUnitEmbFinTwo (formalAdd W)) = 0 := by
  simp [constantCoeff_formalAdd]

/-- The linear coefficient of the reindexed addition series in the variable `0` is `1` — the
`lin_coeff_X` field. -/
@[simp]
theorem coeff_single_zero_renameFin_formalAdd :
    coeff (single (0 : Fin 2) 1) (rename sumUnitEmbFinTwo (formalAdd W)) = 1 := by
  rw [show (single (0 : Fin 2) 1) = embDomain sumUnitEmbFinTwo (single (Sum.inl ()) 1) by
        rw [embDomain_single, sumUnitEmbFinTwo_inl],
    coeff_embDomain_rename]
  exact coeff_single_inl_formalAdd W

/-- The linear coefficient of the reindexed addition series in the variable `1` is `1` — the
`lin_coeff_Y` field. -/
@[simp]
theorem coeff_single_one_renameFin_formalAdd :
    coeff (single (1 : Fin 2) 1) (rename sumUnitEmbFinTwo (formalAdd W)) = 1 := by
  rw [show (single (1 : Fin 2) 1) = embDomain sumUnitEmbFinTwo (single (Sum.inr ()) 1) by
        rw [embDomain_single, sumUnitEmbFinTwo_inr],
    coeff_embDomain_rename]
  exact coeff_single_inr_formalAdd W

/-- Substituting into the reindexed addition series is substituting the reindexed family into
`formalAdd`. This is what carries an identity proved over `Unit ⊕ Unit` — associativity, in
particular — to the `Fin 2` shape Mathlib's `FormalGroup.assoc` is stated in. -/
theorem subst_renameFin_formalAdd {υ : Type*} {g : Fin 2 → MvPowerSeries υ R}
    (hg : HasSubst g) :
    (rename sumUnitEmbFinTwo (formalAdd W)).subst g = (formalAdd W).subst (g ∘ sumUnitEmbFinTwo) :=
  subst_rename _ _ hg

end WeierstrassCurve
