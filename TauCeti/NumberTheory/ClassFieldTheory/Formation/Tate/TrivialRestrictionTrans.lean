/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Restriction
import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Trans

/-!
# Restriction of trivial coefficients in a tower

For a tower of finite normal layers, restriction on integral Tate cohomology composes in every
integer degree. This supplies the trivial-coefficient side of the tower compatibility used by
the Tate isomorphism of a class formation.

In positive degrees these maps agree with ordinary group-cohomology restriction along the
inclusion of Galois groups, and below degree minus one with the transfer in group homology. In
degree zero the map is the identity on integral representatives, while degree minus one vanishes
for integral coefficients.

## Main results

* `TauCeti.ClassFieldTheory.LayerRestriction.trivialTateRes_trans`: trivial-coefficient Tate
  restriction is functorial along a tower of restrictions, in every integer degree.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§2–4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {a b c : NormalLayer G}

attribute [local instance] instFintypeRange

/-! ### Degree zero -/

private theorem trivialTateRes_zero_H0π {small big : NormalLayer G} (T : LayerRestriction small big)
    (x : (Rep.trivial ℤ big.Gal ℤ).ρ.invariants) :
    T.trivialTateRes 0 (TauCeti.TateCohomology.H0π _ x) =
      TauCeti.TateCohomology.H0π (Rep.trivial ℤ small.Gal ℤ) ⟨(x : ℤ), fun _ ↦ rfl⟩ := by
  rw [trivialTateRes_zero, ModuleCat.comp_apply, TauCeti.TateCohomology.H0π_comp_H0Res_apply]
  exact (congrArg (T.trivialTateRangeIso 0).inv
    (T.trivialTateRangeIso_hom_H0π ⟨(x : ℤ), fun _ ↦ rfl⟩).symm).trans (Iso.hom_inv_id_apply _ _)

/-! ### Positive degrees -/

private def trivialCohomologyRes {small big : NormalLayer G} (T : LayerRestriction small big)
    (n : ℕ) :
    groupCohomology (Rep.trivial ℤ big.Gal ℤ) n ⟶ groupCohomology (Rep.trivial ℤ small.Gal ℤ) n :=
  -- Restricting the trivial representation gives the trivial one on the nose, so the coefficient
  -- map is `eqToHom rfl`.
  groupCohomology.map T.galHom (eqToHom rfl) n

private theorem trivialCohomologyRes_trans (T : LayerRestriction a b) (T' : LayerRestriction b c)
    (n : ℕ) : trivialCohomologyRes (T.trans T') n =
      trivialCohomologyRes T' n ≫ trivialCohomologyRes T n :=
  (groupCohomology.map_congr (T.galHom_trans T') rfl n).trans (groupCohomology.map_comp ..)

@[reassoc]
private theorem trivialTateRes_comp_isoGroupCohomology_hom_eq_trivialCohomologyRes
    {small big : NormalLayer G} (T : LayerRestriction small big) (n : ℕ) [NeZero n] :
    T.trivialTateRes n ≫
        (TateCohomology.isoGroupCohomology n).hom.app (Rep.trivial ℤ small.Gal ℤ) =
      (TateCohomology.isoGroupCohomology n).hom.app (Rep.trivial ℤ big.Gal ℤ) ≫
        trivialCohomologyRes T n :=
  -- The square for `trivialTateRes` lands in the cohomology of the image subgroup; the range
  -- comparison carries it back to the smaller Galois group, and `map_comp` merges the two maps.
  ((Iso.eq_comp_inv _).2 <| (Category.assoc ..).trans <|
      (congrArg _ (T.trivialTateRangeIso_hom_comp_isoGroupCohomology_hom n).symm).trans
        (T.trivialTateRes_comp_isoGroupCohomology_hom n)).trans <|
    (Category.assoc ..).trans <| congrArg _ (groupCohomology.map_comp ..).symm

/-! ### Degrees below minus one -/

private theorem trivialTateRangeIso_hom_negSucc_succ {small big : NormalLayer G}
    (T : LayerRestriction small big) (n : ℕ) : (T.trivialTateRangeIso (Int.negSucc (n + 1))).hom =
      TauCeti.TateCohomology.map (e := MonoidHom.ofInjective T.galHom_injective) (φ := LinearMap.id)
        ⟨fun _ _ ↦ rfl⟩ (Int.negSucc (n + 1)) := by
  rw [← cancel_mono ((TateCohomology.isoGroupHomology _ (n + 1) (Int.negSucc_eq _)).hom.app _),
    TauCeti.TateCohomology.map_comp_isoGroupHomology_hom]
  exact (T.trivialTateRangeIso_hom_comp_isoGroupHomology_hom n).trans <| congrArg _ <|
    groupHomology.map_congr rfl (by ext; simpa using T.trivialRangeRepHom_apply 1) _

attribute [local instance] Subgroup.fintypeOfFinite in
private theorem trivialTateRes_negSucc_succ_trans (T : LayerRestriction a b)
    (T' : LayerRestriction b c) (n : ℕ) : (T.trans T').trivialTateRes (Int.negSucc (n + 1)) =
      T'.trivialTateRes (Int.negSucc (n + 1)) ≫ T.trivialTateRes (Int.negSucc (n + 1)) := by
  simp only [trivialTateRes_negSucc_succ, Category.assoc]
  -- The transfer is transitive along the image of the tower of Galois groups...
  rw [← TauCeti.TateCohomology.negSuccRes_trans_assoc _ (galHom_range_trans_le T T')]
  refine congrArg (_ ≫ ·) ((Iso.eq_inv_comp _).2 ?_)
  -- ...and compatible with the identification of the middle Galois group with its image.
  simp only [trivialTateRangeIso_hom_negSucc_succ,
    TauCeti.TateCohomology.map_comp_negSuccRes_assoc _ (MonoidHom.ofInjective T'.galHom_injective) _
      (galHom_range_map_ofInjective T T') (n + 1)]
  refine congrArg (_ ≫ ·) ?_
  -- It remains to compose the identifications of Galois groups and coefficients along the tower.
  rw [TauCeti.TateCohomology.map_comp_assoc, Iso.comp_inv_eq, Iso.eq_inv_comp]
  -- `rw [trivialTateRangeIso_hom_negSucc_succ]` would be far slower here than `simp only`.
  simp only [trivialTateRangeIso_hom_negSucc_succ, TauCeti.TateCohomology.map_comp]
  -- The coefficient maps are all the identity, so only the Galois groups need comparing.
  refine TauCeti.TateCohomology.map_congr (MulEquiv.ext fun γ ↦ Subtype.ext ?_) rfl _
  simp [TauCeti.Subgroup.coe_congrOfMapEq_apply, MonoidHom.ofInjective_apply, galHom_trans T T']

-- The positive degrees of `trivialTateRes_trans`, where restriction is group-cohomology
-- restriction along the inclusion of Galois groups.
private theorem trivialTateRes_natCast_trans (T : LayerRestriction a b) (T' : LayerRestriction b c)
    (n : ℕ) [NeZero n] :
    (T.trans T').trivialTateRes n = T'.trivialTateRes n ≫ T.trivialTateRes n := by
  rw [← cancel_mono ((TateCohomology.isoGroupCohomology n).hom.app (Rep.trivial ℤ a.Gal ℤ)),
    Category.assoc, trivialTateRes_comp_isoGroupCohomology_hom_eq_trivialCohomologyRes,
    trivialTateRes_comp_isoGroupCohomology_hom_eq_trivialCohomologyRes,
    trivialCohomologyRes_trans T T']
  exact (trivialTateRes_comp_isoGroupCohomology_hom_eq_trivialCohomologyRes_assoc T' n _).symm

/-- **Trivial-coefficient Tate restriction is functorial along a tower of restrictions**, in every
integer degree. For fields `F ⊆ E ⊆ E' ⊆ K`, with `T'` restricting `K/F` to `K/E` and `T`
restricting `K/E` to `K/E'`, restricting Tate cohomology with trivial integral coefficients
directly from `K/F` to `K/E'` agrees with restricting from `K/F` to `K/E` and then to `K/E'`.

This is the trivial-coefficient counterpart of `tateRes_trans_eq_comp`. -/
-- Not `@[simp]`: `LayerRestriction` is a `Prop`, so the left-hand side does not mention `T`, `T'`
-- or the middle layer, and `simp` could never instantiate them.
@[reassoc]
theorem trivialTateRes_trans (T : LayerRestriction a b) (T' : LayerRestriction b c) (r : ℤ) :
    (T.trans T').trivialTateRes r = T'.trivialTateRes r ≫ T.trivialTateRes r := by
  match r with
  | 0 =>
    -- In degree zero, restriction is the identity on integral representatives.
    ext x
    induction x using TauCeti.TateCohomology.H0_induction_on with
    | h y =>
      rw [ModuleCat.comp_apply, trivialTateRes_zero_H0π, trivialTateRes_zero_H0π,
        trivialTateRes_zero_H0π]
  | (n + 1 : ℕ) => exact trivialTateRes_natCast_trans T T' (n + 1)
  | -1 =>
    -- Degree minus one vanishes for integral coefficients.
    ext x
    exact (TauCeti.TateCohomology.subsingleton_tateCohomology_negOne_trivial_int a.Gal).elim _ _
  | .negSucc (n + 1) => exact trivialTateRes_negSucc_succ_trans T T' n

end TauCeti.ClassFieldTheory.LayerRestriction
