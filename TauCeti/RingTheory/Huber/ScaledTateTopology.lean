/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RingTheory.Huber.RestrictedPowerSeries

/-!
# The scaled topology on the Tate algebra

For a nonarchimedean ring `A` and a scaling parameter `f : A`, this file puts on the restricted
power series `A⟨X⟩` the topology in which a series is small when its *scaled* coefficients
`fⁿ aₙ` converge coefficientwise: it is the topology induced along the substitution `X ↦ f X`
from the product topology, so a basic neighbourhood of zero constrains only *finitely many*
scaled coefficients. That is weaker than Wedhorn's `U⟨X⟩`, which constrains all of them, and is
part of why the two constructions differ — see below.

## Main definitions

* `TauCeti.Huber.scaleIncl`: the substitution `X ↦ f X`, which is Mathlib's
  `MvPowerSeries.rescale` at a constant scaling family, restricted to `A⟨X⟩`.
* `TauCeti.Huber.scaledTateTopology`: the topology induced along `scaleIncl f`.

## Main results

* `TauCeti.Huber.scaledTateTopology_isTopologicalRing`: it is a ring topology.
* `TauCeti.Huber.scaledTateTopology_nonarchimedean`: it is nonarchimedean, so it has a basis of
  open additive subgroups at zero.
* `TauCeti.Huber.continuous_algebraMap_scaledTateTopology`: the constant-series embedding
  `A → A⟨X⟩` is continuous for it.

## This is not Wedhorn's `A⟨X⟩_T`

Wedhorn's weighted restricted series (*Adic Spaces*, Remark and Definition 5.48, equation
(5.6.1)) is a different object in two ways. Its carrier is a subring of `A[[X]]` cut out by

```text
A⟨X⟩_T := { ∑ aν Xν ; aν ∈ Tν · U for every open subgroup U of A and almost all ν },
```

with fundamental neighbourhoods `U⟨X⟩ := { ∑ aν Xν ∈ A⟨X⟩_T ; aν ∈ Tν · U for all ν }`. So the
weight multiplies the neighbourhood `U`, not the coefficient, and the carrier varies with `T`
— `A⟨X⟩` is by definition the case `T = {1}` (Wedhorn, Example 5.54).

What is built here instead keeps the `T = {1}` carrier `A⟨X⟩` and transports its topology along
`X ↦ f X`, giving the conditions `fⁿ aₙ ∈ U`. The two agree only under extra invertibility
assumptions on `f`, which are not made here and for which no equivalence is proved. Anything
claiming to formalise (5.6.1) must build the weighted carrier directly.

## Provenance

This is a port of the first part of AINTLIB's `TateAlgebraWedhorn.lean`, at commit `d9f2fbbb`,
covering its `scaleHom` through `tateTopologyT_continuous_algebraMap`. The changes are: the
declarations move into the `TauCeti.Huber` namespace and are renamed after their conclusions;
`A⟨X⟩` is spelled `restrictedMvPowerSeriesSubring 1 A` rather than through a `TateAlgebra`
abbreviation; the module opts into the Lean module system; and the identification of this
construction with Wedhorn's Definition 5.48, which the source asserts, is retracted for the
reason given above.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Remark and Definition 5.48 and Example 5.54, for
  the weighted ring this construction is *not*.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), commit `d9f2fbbb`,
  `projects/AdicSpaces/Adic spaces/TateAlgebraWedhorn.lean`.
-/

open MvPowerSeries

namespace TauCeti.Huber

public section

section Scaling

variable {A : Type*} [CommRing A]

end Scaling

section Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- The scaling homomorphism restricted to the restricted power series `A⟨X⟩`. The weighted
topology is the one this map induces. -/
noncomputable def scaleIncl (f : A) :
    restrictedMvPowerSeriesSubring 1 A →+* MvPowerSeries (Fin 1) A :=
  (MvPowerSeries.rescale (fun _ : Fin 1 ↦ f)).comp
    (restrictedMvPowerSeriesSubring 1 A).subtype

@[simp]
theorem scaleIncl_apply (f : A) (g : restrictedMvPowerSeriesSubring 1 A) (s : Fin 1 →₀ ℕ) :
    scaleIncl f g s = f ^ (s 0) * (g : MvPowerSeries (Fin 1) A) s := by
  change MvPowerSeries.coeff s (MvPowerSeries.rescale (fun _ : Fin 1 ↦ f)
    (g : MvPowerSeries (Fin 1) A)) = _
  rw [MvPowerSeries.coeff_rescale, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero f),
    Fin.prod_univ_one]
  rfl

/-! ### The scaled topology -/

/-- The topology on `A⟨X⟩` pulled back along `X ↦ f X` from the product topology: a series is
near zero when finitely many prescribed scaled coefficients `fⁿ aₙ` are.  See the module
docstring: this is *not* Wedhorn's `A⟨X⟩_T`. -/
@[reducible]
noncomputable def scaledTateTopology (f : A) :
    TopologicalSpace (restrictedMvPowerSeriesSubring 1 A) :=
  TopologicalSpace.induced (scaleIncl f) (WithPiTopology.instTopologicalSpace A)

/-- The scaled topology is a ring topology: it is induced along a ring homomorphism from the
product topology, which is one. -/
theorem scaledTateTopology_isTopologicalRing (f : A) :
    @IsTopologicalRing _ (scaledTateTopology f) _ := by
  let _ : TopologicalSpace (MvPowerSeries (Fin 1) A) := WithPiTopology.instTopologicalSpace A
  have : IsTopologicalRing (MvPowerSeries (Fin 1) A) :=
    WithPiTopology.instIsTopologicalRing (Fin 1) A
  let _ : TopologicalSpace (restrictedMvPowerSeriesSubring 1 A) := scaledTateTopology f
  have := topologicalAddGroup_induced (scaleIncl f)
  have : ContinuousMul (restrictedMvPowerSeriesSubring 1 A) := continuousMul_induced (scaleIncl f)
  exact { continuous_add := continuous_add
          continuous_mul := continuous_mul
          continuous_neg := continuous_neg }

/-- The scaled topology is nonarchimedean: every neighbourhood of zero contains an open
additive subgroup, obtained by pulling back a finite product of such subgroups of `A`. -/
theorem scaledTateTopology_nonarchimedean (f : A) :
    @NonarchimedeanRing _ _ (scaledTateTopology f) := by
  let _ : TopologicalSpace (MvPowerSeries (Fin 1) A) := WithPiTopology.instTopologicalSpace A
  have : IsTopologicalRing (MvPowerSeries (Fin 1) A) :=
    WithPiTopology.instIsTopologicalRing (Fin 1) A
  let _ : TopologicalSpace (restrictedMvPowerSeriesSubring 1 A) := scaledTateTopology f
  have := scaledTateTopology_isTopologicalRing f
  constructor
  intro U hU
  rw [@nhds_induced _ _ (WithPiTopology.instTopologicalSpace A) (scaleIncl f) 0,
    Filter.mem_comap] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  rw [map_zero] at hW
  change W ∈ @nhds _ (@Pi.topologicalSpace (Fin 1 →₀ ℕ) (fun _ ↦ A) fun _ ↦ ‹_›) 0 at hW
  rw [nhds_pi] at hW
  simp only [show ∀ i : Fin 1 →₀ ℕ, (0 : (Fin 1 →₀ ℕ) → A) i = (0 : A) from fun _ ↦ rfl] at hW
  obtain ⟨I, hI, t, ht, hIt⟩ := Filter.mem_pi.mp hW
  have hVi : ∀ i : Fin 1 →₀ ℕ, ∃ V : OpenAddSubgroup A, (V : Set A) ⊆ t i := fun i ↦
    NonarchimedeanRing.is_nonarchimedean (t i) (ht i)
  choose V hV using hVi
  -- Build the open subgroup upstairs as a finite product, then pull it back: both steps are
  -- Mathlib's (`AddSubgroup.pi`, `isOpen_set_pi`, `OpenAddSubgroup.comap`).
  let S : OpenAddSubgroup (MvPowerSeries (Fin 1) A) :=
    ⟨AddSubgroup.pi I fun i ↦ (V i).toAddSubgroup, isOpen_set_pi hI fun i _ ↦ (V i).isOpen⟩
  exact ⟨S.comap (scaleIncl f).toAddMonoidHom continuous_induced_dom,
    fun g hg ↦ hWU (hIt fun i hi ↦ hV i (hg i hi))⟩

/-- The constant-series embedding `A → A⟨X⟩` is continuous for the scaled topology. -/
theorem continuous_algebraMap_scaledTateTopology (f : A) :
    @Continuous _ _ _ (scaledTateTopology f)
      (algebraMap A (restrictedMvPowerSeriesSubring 1 A)) := by
  let _ : TopologicalSpace (restrictedMvPowerSeriesSubring 1 A) := scaledTateTopology f
  let _ : TopologicalSpace (MvPowerSeries (Fin 1) A) := WithPiTopology.instTopologicalSpace A
  refine continuous_induced_rng.mpr ?_
  -- `rescale` fixes the constant series, which is `AlgHom.commutes` for Mathlib's
  -- `MvPowerSeries.rescaleAlgHom`; no coefficientwise case split is needed.
  have hconst : scaleIncl f ∘ (algebraMap A (restrictedMvPowerSeriesSubring 1 A))
      = algebraMap A (MvPowerSeries (Fin 1) A) := by
    funext a
    change MvPowerSeries.rescale (fun _ : Fin 1 ↦ f)
      ((algebraMap A (restrictedMvPowerSeriesSubring 1 A) a : MvPowerSeries (Fin 1) A)) = _
    rw [coe_algebraMap_restrictedMvPowerSeriesSubring,
      ← MvPowerSeries.rescaleAlgHom_apply (fun _ : Fin 1 ↦ f)]
    exact (MvPowerSeries.rescaleAlgHom (fun _ : Fin 1 ↦ f)).commutes a
  rw [hconst]
  exact WithPiTopology.continuous_C

end Topology

end

end TauCeti.Huber
