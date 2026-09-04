/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Laurent
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

/-!
# Comparing the weighted and restricted vocabularies

`TauCeti.Huber.weightedRestrictedSubring_one_weight` says that at the trivial weight family
`Tᵢ = {1}` the weighted ring `A⟨X⟩_T` *is* the ordinary ring of restricted power series. That is an
equality of subrings, so it transports elements along
`RingEquiv.subringCongr`; what it does not say is where the generators go. This file says it: the
weighted variable is the restricted variable, and the weighted constant is the algebra map.

Without these, a result proved in one vocabulary has to be re-transported by hand at every use.
The two are genuinely used in different places — `TauCeti.RingTheory.Huber.Restricted.Laurent` and
`TauCeti.RingTheory.Huber.Restricted.Flat` work with `restrictedMvPowerSeriesSubring`, while
`TauCeti.RingTheory.Huber.StronglyNoetherian` and the weighted-evaluation development work with
`weightedRestrictedSubring` — so Wedhorn's Proposition 8.30, which needs the Laurent flatness
results of the first inside the localisation machinery of the second, crosses between them.

## Main results

* `TauCeti.Huber.subringCongr_one_weight_weightedX`: the weighted variable is `restrictedX`.
* `TauCeti.Huber.subringCongr_one_weight_weightedC`: the weighted constant is the algebra map.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 5.54 and
  Proposition 8.30.
-/

public section

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The weighted variable is the restricted variable.** Transporting `weightedX` along the
identification of the trivial-weight subring with the restricted subring gives `restrictedX`. -/
@[simp]
theorem subringCongr_one_weight_weightedX :
    RingEquiv.subringCongr (weightedRestrictedSubring_one_weight (k := 1) (A := A))
        (weightedX _ isWeightFamily_one_weight 0)
      = restrictedX :=
  Subtype.ext (by simp)

/-- **The weighted constant is the algebra map.** Transporting `weightedC a` along the same
identification gives the image of `a` under the structure map of the restricted subring. -/
@[simp]
theorem subringCongr_one_weight_weightedC (a : A) :
    RingEquiv.subringCongr (weightedRestrictedSubring_one_weight (k := k) (A := A))
        (weightedC _ isWeightFamily_one_weight a)
      = algebraMap A (restrictedMvPowerSeriesSubring k A) a :=
  Subtype.ext (by simp [MvPowerSeries.algebraMap_apply])

end TauCeti.Huber

end
