/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.RingTheory.Localization.OpenSubring

/-!
# An open subring has the same spectrum on a topologically nilpotent basic open

Let `B` be an **open** subring of a topological ring `A`, and let `s : B` be topologically
nilpotent in `A`. Taking prime spectra turns the inclusion around into
`PrimeSpectrum.comap B.subtype : Spec A → Spec B`, and Mathlib's `PrimeSpectrum.comap_basicOpen`
already sends the basic open `D(s) ⊆ Spec A` into `D(s) ⊆ Spec B`. This file proves that the
resulting restriction is a **homeomorphism**.

That is where openness of `B` and nilpotence of `s` enter, and they enter only through
`TauCeti.Localization.awayRingEquivOfIsTopologicallyNilpotent`: inverting `s` does not distinguish
`B` from `A`, so the two localisations have the same spectrum, and each basic open *is* the
spectrum of the corresponding localisation.

## Implementation notes

Everything is transported along the commuting square of ring maps

`B → A → A_s`  =  `B → B_s → A_s`,

which is `IsLocalization.map_comp`. Applying `PrimeSpectrum.comap` reverses it into
`PrimeSpectrum.comap_subtype_comap_algebraMap`, whose two horizontal maps are open embeddings onto
the two basic opens (`PrimeSpectrum.localization_away_isOpenEmbedding` and
`localization_away_comap_range`, packaged here as the private `spectrumAwayHomeomorph`) and whose
remaining vertical map is a homeomorphism because the ring map is bijective.

`spectrumAwayHomeomorph` is deliberately private: Mathlib has both of its ingredients but not the
bundled homeomorphism, and adding that in general is a different topic from this file's.

The localisations stay arbitrary `IsLocalization.Away` targets where they are quantified over,
matching `TauCeti.RingTheory.Localization.OpenSubring`; the statements that do not mention them
are proved by instantiating `Localization.Away`.

## Source

Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), the spectral step inside the proof of Lemma 7.44(1):
for a non-open prime `q` of `B` there is a topologically nilpotent `s ∉ q`, and then
`f⁻¹(Spec B_s) = Spec A_s`.

**Only that per-element step is formalised here.** Lemma 7.44(1) in full also identifies the open
primes of `A` with the preimages of the open primes of `B`, and glues these homeomorphisms over all
topologically nilpotent `s` into a single homeomorphism of the two complements. Neither is proved
in this file.

## Main results

* `PrimeSpectrum.basicOpenHomeomorph`: the homeomorphism of basic opens, with
  `PrimeSpectrum.basicOpenHomeomorph_apply_coe` identifying its map as `comap B.subtype`.
* `PrimeSpectrum.bijOn_comap_subtype_basicOpen`: its set-level form, from which
  `Set.BijOn.image_eq` and `Set.BijOn.injOn` give the image equality and injectivity.
-/

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A] [ContinuousMul A]
variable {B : Subring A} {s : B}

namespace PrimeSpectrum

open TopologicalSpace TauCeti.Localization

omit [TopologicalSpace A] [ContinuousMul A] in
/-- Taking spectra of `B → A → A_s` `=` `B → B_s → A_s`. This is the square along which every
statement in this file is transported. -/
theorem comap_subtype_comap_algebraMap (Bs As : Type*) [CommSemiring Bs] [CommSemiring As]
    [Algebra B Bs] [IsLocalization.Away s Bs]
    [Algebra A As] [IsLocalization.Away (B.subtype s) As] (x : PrimeSpectrum As) :
    comap B.subtype (comap (algebraMap A As) x) =
      comap (algebraMap B Bs) (comap (IsLocalization.Away.map Bs As B.subtype s) x) := by
  have hmap : (IsLocalization.Away.map Bs As B.subtype s).comp (algebraMap B Bs) =
      (algebraMap A As).comp B.subtype := IsLocalization.map_comp _
  rw [← comap_comp_apply, ← comap_comp_apply, hmap]

/-- The spectrum of a localisation away from `r`, as the basic open of `r`. -/
private noncomputable def spectrumAwayHomeomorph {R : Type*} [CommSemiring R] (S : Type*)
    [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S] :
    PrimeSpectrum S ≃ₜ (basicOpen r : Set (PrimeSpectrum R)) :=
  (localization_away_isOpenEmbedding S r).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (localization_away_comap_range S r))

@[simp]
private theorem spectrumAwayHomeomorph_apply_coe {R : Type*} [CommSemiring R] (S : Type*)
    [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S] (x : PrimeSpectrum S) :
    (spectrumAwayHomeomorph S r x : PrimeSpectrum R) = comap (algebraMap R S) x :=
  rfl

/-- **Wedhorn's Lemma 7.44(1), its single-element spectral step.** For `B` an open subring of `A`
and `s : B` topologically nilpotent in `A`, contracting primes along `B → A` is a homeomorphism
from the basic open of `s` in `Spec A` onto the basic open of `s` in `Spec B`.

Both sides are the spectrum of a localisation away from `s`, and inverting `s` cannot tell `B`
from `A` — that is `TauCeti.Localization.awayRingEquivOfIsTopologicallyNilpotent`, and it is the
only place the hypotheses are used. See `basicOpenHomeomorph_apply_coe` for the underlying map. -/
noncomputable def basicOpenHomeomorph (hB : IsOpen (B : Set A))
    (hs : IsTopologicallyNilpotent (s : A)) :
    (basicOpen (B.subtype s) : Set (PrimeSpectrum A)) ≃ₜ (basicOpen s : Set (PrimeSpectrum B)) :=
  (spectrumAwayHomeomorph (Localization.Away (B.subtype s)) (B.subtype s)).symm.trans <|
    (IsHomeomorph.homeomorph _
        (isHomeomorph_comap_of_bijective (awayMap_bijective (Localization.Away s)
          (Localization.Away (B.subtype s)) hB hs))).trans <|
      spectrumAwayHomeomorph (Localization.Away s) s

@[simp]
theorem basicOpenHomeomorph_apply_coe (hB : IsOpen (B : Set A))
    (hs : IsTopologicallyNilpotent (s : A))
    (x : (basicOpen (B.subtype s) : Set (PrimeSpectrum A))) :
    (basicOpenHomeomorph hB hs x : PrimeSpectrum B) = comap B.subtype x := by
  obtain ⟨y, rfl⟩ :=
    (spectrumAwayHomeomorph (Localization.Away (B.subtype s)) (B.subtype s)).surjective x
  simp only [basicOpenHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
    IsHomeomorph.homeomorph_apply, spectrumAwayHomeomorph_apply_coe]
  exact (comap_subtype_comap_algebraMap (Localization.Away s)
    (Localization.Away (B.subtype s)) y).symm

/-- **The set-level form of `basicOpenHomeomorph`.** Contraction along `B → A` restricts to a
bijection between the two basic opens of `s`; `Set.BijOn.image_eq` turns this into the image
equality, and `Set.BijOn.injOn` into injectivity on the basic open. -/
theorem bijOn_comap_subtype_basicOpen (hB : IsOpen (B : Set A))
    (hs : IsTopologicallyNilpotent (s : A)) :
    Set.BijOn (comap B.subtype) (basicOpen (B.subtype s) : Set (PrimeSpectrum A))
      (basicOpen s : Set (PrimeSpectrum B)) := by
  refine ⟨fun x hx ↦ ?_, fun x hx y hy h ↦ ?_, fun z hz ↦ ?_⟩
  · rw [← basicOpenHomeomorph_apply_coe hB hs ⟨x, hx⟩]
    exact (basicOpenHomeomorph hB hs ⟨x, hx⟩).2
  · refine congrArg Subtype.val ((basicOpenHomeomorph hB hs).injective
      (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext ?_))
    rw [basicOpenHomeomorph_apply_coe, basicOpenHomeomorph_apply_coe]
    exact h
  · obtain ⟨w, hw⟩ := (basicOpenHomeomorph hB hs).surjective ⟨z, hz⟩
    exact ⟨w.1, w.2, by rw [← basicOpenHomeomorph_apply_coe hB hs w, hw]⟩

end PrimeSpectrum

end
