/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Renaming a one-variable power series into a single variable

`MvPowerSeries.rename (fun _ : Unit => s)` embeds a one-variable power series into
`MvPowerSeries τ R` as a series in the single variable `s`. This file records the coefficients
of the result: they vanish off the powers of `s`, where they agree with the coefficients of the
original series.

## Main results

* `MvPowerSeries.coeff_rename_const`: the coefficients of `rename (fun _ => s)`.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean`, the private lemma `coeff_rename_single`.
There it is stated only where it is used; it carries no elliptic content, so it is recorded
here as a lemma about `MvPowerSeries.rename` on its own.
-/

public section

namespace MvPowerSeries

variable {τ R : Type*} [CommSemiring R] [DecidableEq τ]

/-- The coefficients of a one-variable power series renamed into the single variable `s`: the
coefficient of a monomial `d` is the `d s`-th coefficient of the original series if `d` is a
power of `s`, and `0` otherwise. -/
theorem coeff_rename_const (s : τ) (w : PowerSeries R) (d : τ →₀ ℕ) :
    coeff d (rename (fun _ : Unit => s) w) =
      if d = Finsupp.single s (d s) then PowerSeries.coeff (d s) w else 0 := by
  split_ifs with h
  · have hd : d = Finsupp.embDomain (⟨fun _ => s, fun _ _ _ => rfl⟩ : Unit ↪ τ)
        (Finsupp.single () (d s)) := by
      rw [Finsupp.embDomain_single]
      exact h
    have h1 := coeff_embDomain_rename (⟨fun _ => s, fun _ _ _ => rfl⟩ : Unit ↪ τ) w
      (Finsupp.single () (d s))
    rw [← hd] at h1
    exact h1
  · refine coeff_rename_eq_zero _ _ fun ⟨y, hy⟩ => h ?_
    rw [← hy, Finsupp.unique_single y, Finsupp.mapDomain_single]
    simp

end MvPowerSeries
