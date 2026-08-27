/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Substituting into a renamed multivariate power series

Renaming the variables of a multivariate power series and substituting for them are the two ways
of changing what the variables of a series stand for, and they interact in the obvious way: a
substitution applied after a renaming is the substitution along the renamed index.

Mathlib has both operations and the law that lets them be compared — `rename_eq_subst`, which
says a renaming *is* the substitution sending each variable to a variable — but not the
comparison itself, which is what a caller reindexing a series needs.

## Main results

* `MvPowerSeries.subst_rename`: substituting into `rename e p` reindexes the family, i.e. it is
  substituting `g ∘ e` into `p`.
* `sumUnitEmbFinTwo`: the reindexing `Unit ⊕ Unit ↪ Fin 2`, for presenting a series in two
  separately-named variables over `Fin 2`.

## Provenance

No external source: the statement is a gap in Mathlib's `MvPowerSeries` API and the proof is
three steps of that same API (`rename_eq_subst`, `HasSubst.X_comp`, `subst_comp_subst_apply`).
It is recorded here rather than inside its caller because it carries no elliptic content.
-/

public section

/-- **The reindexing `Unit ⊕ Unit ↪ Fin 2`**, sending the left summand to `0` and the right to `1`.

Two separately-named variables and the two variables of `Fin 2` are the two ways a two-variable
object gets indexed, and translating between them is pure bookkeeping — Mathlib has
`boolEquivPUnitSumPUnit` and `finSumFinEquiv` but nothing of this shape, and composing those two
would go through `Bool` and a `PUnit` universe adjustment for no gain.

It is an `Embedding` rather than a bare function because injectivity is what turns a coefficient
under `MvPowerSeries.rename` into an equality rather than a sum over a fibre — see
`MvPowerSeries.coeff_embDomain_rename`. -/
def sumUnitEmbFinTwo : (Unit ⊕ Unit) ↪ Fin 2 where
  toFun := Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)
  inj' := by decide

@[simp]
theorem sumUnitEmbFinTwo_inl : sumUnitEmbFinTwo (Sum.inl ()) = 0 := by decide

@[simp]
theorem sumUnitEmbFinTwo_inr : sumUnitEmbFinTwo (Sum.inr ()) = 1 := by decide

namespace MvPowerSeries

open Filter

variable {σ τ υ R : Type*} [CommRing R]

/-- **Substituting into a renamed series reindexes the family**: `rename e p` followed by
substituting `g` is `p` with `g ∘ e` substituted.

Both hypotheses are the ones the two operations already carry: `rename` needs `e` to have finite
fibres (`TendstoCofinite`) for the renamed coefficients to be well defined, and `subst` needs
`HasSubst g`. Nothing is assumed about `e` beyond that — in particular it need not be injective,
since a collision merely substitutes the same series for two variables. -/
theorem subst_rename (e : σ → τ) [TendstoCofinite e] (p : MvPowerSeries σ R)
    {g : τ → MvPowerSeries υ R} (hg : HasSubst g) :
    (rename e p).subst g = p.subst (g ∘ e) := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hg]
  simp [subst_X hg, Function.comp_def]

end MvPowerSeries
