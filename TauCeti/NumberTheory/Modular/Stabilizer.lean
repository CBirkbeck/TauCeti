/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction
public import TauCeti.GroupTheory.GroupAction.Stabilizer
public import TauCeti.NumberTheory.Modular.Orbits

-- these two serve only the private centre computation, so they stay off the public surface
import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Orders of the point stabilisers of the modular group

The stabiliser of a point of `ℍ` in `SL(2, ℤ)` is finite, and its order depends only on the
orbit. Off the two elliptic orbits that order is `2` — the centre `±1`, which acts trivially —
while on the orbit of `i` it is `4` and on the orbit of `ρ` it is `6`. Dividing by the centre
these are the `PSL(2, ℤ)`-orders `e_i = 2`, `e_ρ = 3` and `e_P = 1` elsewhere, the weights the
valence formula attaches to its orbits.

Mathlib classifies the stabilising matrices (`ModularGroup.stabilizer_I`,
`ModularGroup.stabilizer_ρ`, `ModularGroup.stabilizer_of_ne`), but only at a point of the closed
fundamental domain `𝒟`. Added here is the passage to an arbitrary point of `ℍ`, which
`ModularGroup.exists_smul_mem_fd` and conjugation supply, together with the resulting counts.

The three orbit-level counts are stated with their hypotheses on the class of `z` in
`MulAction.orbitRel.Quotient SL(2, ℤ) ℍ`, rather than on a fundamental-domain representative,
because that is the form the valence formula's index type consumes: its non-elliptic orbits are
literally the `q` with `q ≠ ⟦i⟧` and `q ≠ ⟦ρ⟧`.

## Main declarations

* `TauCeti.ModularGroup.finite_stabilizer`: every point stabiliser is finite, so the elliptic
  order is defined at every point of `ℍ`.
* `TauCeti.ModularGroup.card_stabilizer_I` and `TauCeti.ModularGroup.card_stabilizer_ρ`: the
  orders `4` and `6` at the two elliptic points themselves.
* `TauCeti.ModularGroup.card_stabilizer_of_orbit_eq_I` and
  `TauCeti.ModularGroup.card_stabilizer_of_orbit_eq_ρ`: the same orders everywhere on those two
  orbits.
* `TauCeti.ModularGroup.card_stabilizer_eq_two_of_orbit_ne_I_of_orbit_ne_ρ`: order `2` on every
  other orbit.
* `TauCeti.ModularGroup.card_stabilizer_eq_card_center_mul_card_stabilizer_psl`: for any
  `Γ ≤ SL(2, ℤ)`, the stabiliser order in `Γ` splits off the part of the centre that `Γ`
  contains, leaving the projective order in `Γ`'s image in `PSL(2, ℤ)`.
* `TauCeti.ModularGroup.card_center_subgroupOf_eq_two_iff` and
  `TauCeti.ModularGroup.card_center_subgroupOf_eq_one_iff`: that centre factor is `2` exactly when
  `-I ∈ Γ`, and `1` exactly when it is not — the membership decides which case occurs, with
  `TauCeti.ModularGroup.card_center_subgroupOf_eq_one_or_two` the unindexed corollary.
* `TauCeti.ModularGroup.card_stabilizer_eq_two_mul_card_stabilizer_psl`: the projective order is
  the matrix one halved.
* `TauCeti.ModularGroup.card_stabilizer_psl_I`, `TauCeti.ModularGroup.card_stabilizer_psl_ρ` and
  `TauCeti.ModularGroup.card_stabilizer_psl_eq_one_of_orbit_ne_I_of_orbit_ne_ρ`: the resulting
  elliptic orders `e_i = 2`, `e_ρ = 3` and `e_P = 1`.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §2.3 — the elliptic points of `SL(2, ℤ)`
  and their stabiliser orders.
-/

public section

open MulAction UpperHalfPlane ModularGroup

open scoped MatrixGroups Modular

namespace TauCeti

namespace ModularGroup

variable {w z : ℍ}

private theorem finite_stabilizer_of_subset (s : Finset SL(2, ℤ))
    (hs : ∀ g : SL(2, ℤ), g • w = w → g ∈ s) : Finite (stabilizer SL(2, ℤ) w) :=
  (s.finite_toSet.subset fun g hg ↦ hs g hg).to_subtype

private theorem finite_stabilizer_of_smul (g : SL(2, ℤ))
    (h : Finite (stabilizer SL(2, ℤ) (g • z))) : Finite (stabilizer SL(2, ℤ) z) :=
  Finite.of_equiv _ (stabilizerEquivStabilizerOfOrbitRel
    (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit z g))).toEquiv

/-- **Every point stabiliser is finite**, so the elliptic order `e_P` is defined at every point
of `ℍ` and not only inside the fundamental domain. -/
instance finite_stabilizer (z : ℍ) : Finite (stabilizer SL(2, ℤ) z) := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  refine finite_stabilizer_of_smul g ?_
  by_cases hI : g • z = I
  · exact hI ▸ finite_stabilizer_of_subset {1, -1, S, -S} fun _ h ↦ stabilizer_I.mp h
  by_cases hρ : g • z = ρ
  · exact hρ ▸ finite_stabilizer_of_subset _ fun _ h ↦ stabilizer_ρ.mp h
  by_cases hρ' : g • z = (1 : ℝ) +ᵥ ρ
  · -- `ρ + 1` is `T • ρ`, so its stabiliser is conjugate to the one at `ρ`
    rw [hρ', ← modular_T_smul]
    refine finite_stabilizer_of_smul T⁻¹ ?_
    rw [← mul_smul, inv_mul_cancel, one_smul]
    exact finite_stabilizer_of_subset _ fun _ h ↦ stabilizer_ρ.mp h
  · exact finite_stabilizer_of_subset {1, -1} fun _ h ↦ by
      rcases stabilizer_of_ne hg h hI hρ hρ' with rfl | rfl <;> simp

private theorem card_stabilizer_of_coe_eq {s : Finset SL(2, ℤ)}
    (h : (stabilizer SL(2, ℤ) w : Set SL(2, ℤ)) = ↑s) :
    Nat.card (stabilizer SL(2, ℤ) w) = s.card := by
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq]
  simp

-- None of the `SL(2, ℤ)` counts below is `@[simp]`, and none can be: their common
-- left-hand side `Nat.card (stabilizer SL(2, ℤ) z)` is not in simp-normal form, because
-- `MulAction.mem_stabilizer_iff` and `ModularGroup.sl_moeb` rewrite the membership condition
-- underneath the `Nat.card`, so `simpNF` rejects the attribute on every one of them.

/-- **The stabiliser of `i` has order `4`**: the centre `±1` together with `±S`, the inversion
fixing `i`. In `PSL(2, ℤ)` this is the elliptic order `e_i = 2`. -/
theorem card_stabilizer_I : Nat.card (stabilizer SL(2, ℤ) I) = 4 :=
  (card_stabilizer_of_coe_eq (s := {1, -1, S, -S}) (by ext g; simpa using stabilizer_I)).trans
    (by decide)

/-- **The stabiliser of `ρ` has order `6`**: the centre `±1` together with `±ST` and `±T⁻¹S`,
the two rotations of order three fixing `ρ`. In `PSL(2, ℤ)` this is the elliptic order
`e_ρ = 3`. -/
theorem card_stabilizer_ρ : Nat.card (stabilizer SL(2, ℤ) ρ) = 6 :=
  (card_stabilizer_of_coe_eq (s := {1, -1, S * T, -(S * T), T⁻¹ * S, -(T⁻¹ * S)})
    (by ext g; simpa using stabilizer_ρ)).trans (by decide)

/-- **Order `4` everywhere on the orbit of `i`**, not just at `i`: conjugate stabilisers have
equal order, so `card_stabilizer_I` propagates along the orbit. -/
theorem card_stabilizer_of_orbit_eq_I
    (hz : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' I) :
    Nat.card (stabilizer SL(2, ℤ) z) = 4 := by
  obtain ⟨g, rfl⟩ : ∃ g : SL(2, ℤ), g • (I : ℍ) = z := Quotient.exact' hz
  exact (card_stabilizer_smul g I).trans card_stabilizer_I

/-- **Order `6` everywhere on the orbit of `ρ`**, not just at `ρ`; the companion of
`card_stabilizer_of_orbit_eq_I`. -/
theorem card_stabilizer_of_orbit_eq_ρ
    (hz : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' ρ) :
    Nat.card (stabilizer SL(2, ℤ) z) = 6 := by
  obtain ⟨g, rfl⟩ : ∃ g : SL(2, ℤ), g • (ρ : ℍ) = z := Quotient.exact' hz
  exact (card_stabilizer_smul g ρ).trans card_stabilizer_ρ

/-- **Away from the two elliptic orbits the stabiliser is just the centre**, of order `2`, so
`e_P = 1` in `PSL(2, ℤ)`. No fundamental-domain membership is asked of `z`: the exclusions are
read on its orbit, which is what the valence formula's non-elliptic index type carries. -/
theorem card_stabilizer_eq_two_of_orbit_ne_I_of_orbit_ne_ρ (z : ℍ)
    (hI : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' I)
    (hρ : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' ρ) :
    Nat.card (stabilizer SL(2, ℤ) z) = 2 := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  have hq : (Quotient.mk'' (g • z) : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' z :=
    Quotient.sound' ⟨g, rfl⟩
  -- the representative in `𝒟` inherits both exclusions, so Mathlib's classification applies
  have hI' : g • z ≠ I := fun h ↦ hI (hq ▸ (orbit_mk_eq_I_iff hg).mpr h)
  have hρ' : g • z ≠ ρ := fun h ↦ hρ (hq ▸ (orbit_mk_eq_ρ_iff hg).mpr (Or.inl h))
  have hρ'' : g • z ≠ (1 : ℝ) +ᵥ ρ := fun h ↦ hρ (hq ▸ (orbit_mk_eq_ρ_iff hg).mpr (Or.inr h))
  rw [← card_stabilizer_smul g z]
  refine (card_stabilizer_of_coe_eq (s := {1, -1}) ?_).trans (by decide)
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rcases stabilizer_of_ne hg hx hI' hρ' hρ'' with rfl | rfl <;> simp
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [MulAction.mem_stabilizer_iff]

/-! ### The projective orders `e_P` -/

-- the centre of `SL(2, ℤ)` has order two. Built on Mathlib rather than on an explicit `{±1}`
-- computation: the matrix and module special linear groups agree (`toLin'_equiv`), the module
-- one has centre the roots of unity (`centerEquivRootsOfUnity`), and `-1` is a primitive second
-- root over `ℤ`.
private theorem card_center : Nat.card (Subgroup.center SL(2, ℤ)) = 2 := by
  have hroot : IsPrimitiveRoot (-1 : ℤ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  have hrank : max (Module.finrank ℤ (Fin 2 → ℤ)) 1 = 2 := by simp
  rw [Nat.card_congr (Subgroup.centerCongr Matrix.SpecialLinearGroup.toLin'_equiv).toEquiv,
    Nat.card_congr (SpecialLinearGroup.centerEquivRootsOfUnity (R := ℤ) (V := Fin 2 → ℤ)).toEquiv,
    hrank, hroot.card_rootsOfUnity]

/-- **The stabiliser order in `Γ` splits off the part of the centre that `Γ` contains.** For any
`Γ ≤ SL(2, ℤ)`, the order of the stabiliser of `z` in `Γ` is the order of `Γ ⊓ ±1` times the
order of the stabiliser in the image of `Γ` in `PSL(2, ℤ)` — the projective, elliptic order. The
factor is `2` when `-I ∈ Γ` and `1` otherwise, by `card_center_subgroupOf_eq_two_iff` below.

This is the general-level form of the halving below, and it is exactly one application of
`TauCeti.card_stabilizer_eq_card_subgroupOf_mul_card_stabilizer_map`: no quotient action of `Γ`
has to be built, because the image of `Γ` in `PSL(2, ℤ)` is a subgroup of `PSL(2, ℤ)`, which
already acts on `ℍ`. Compatibility of the two actions is definitional, since `PSL(2, R)` is
`SL(2, R) ⧸ center` and `pslMk_smul` is `rfl`. -/
theorem card_stabilizer_eq_card_center_mul_card_stabilizer_psl {Γ : Subgroup SL(2, ℤ)} (z : ℍ) :
    Nat.card (stabilizer Γ z) =
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) *
        Nat.card (stabilizer (Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) z) :=
  TauCeti.card_stabilizer_eq_card_subgroupOf_mul_card_stabilizer_map _ Γ z
    fun _ ↦ UpperHalfPlane.pslMk_smul _ _

-- the centre of `SL(2, ℤ)` is `{±I}`: `Matrix.SpecialLinearGroup.mem_center_iff` presents a
-- central element as a scalar matrix `r • I` with `r ^ 2 = 1`, and `±1` are the only units of `ℤ`
private theorem eq_one_or_neg_one_of_mem_center {A : SL(2, ℤ)}
    (hA : A ∈ Subgroup.center SL(2, ℤ)) : A = 1 ∨ A = -1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  simp only [Fintype.card_fin] at hr
  have h0 : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.mp h0 with h | h
  · have hr1 : r = 1 := by omega
    subst hr1
    exact Or.inl (Subtype.ext (by simpa using hrA.symm))
  · have hr1 : r = -1 := by omega
    subst hr1
    exact Or.inr (Subtype.ext (by simpa using hrA.symm))

private theorem neg_one_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) :=
  Subgroup.mem_center_iff.mpr fun g ↦ by ext i j; simp

private theorem neg_one_ne_one : (-1 : SL(2, ℤ)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, ℤ) ↦ (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp at this

-- the count is between one and two: the identity is always there, and the inclusion of
-- `Γ ⊓ {±I}` into `{±I}` caps it by `card_center`
private theorem card_center_subgroupOf_le_two (Γ : Subgroup SL(2, ℤ)) :
    0 < Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) ∧
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) ≤ 2 := by
  -- `mem_subgroupOf` is what moves the membership across the inclusion
  have hinj : Function.Injective
      (fun x : (Subgroup.center SL(2, ℤ)).subgroupOf Γ ↦
        (⟨((x : Γ) : SL(2, ℤ)), Subgroup.mem_subgroupOf.mp x.2⟩ : Subgroup.center SL(2, ℤ))) := by
    intro a b h
    rw [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  have h2 : Nat.card (Subgroup.center SL(2, ℤ)) = 2 := card_center
  have : Finite (Subgroup.center SL(2, ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; omega)
  have : Finite ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) := Finite.of_injective _ hinj
  have hle : Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) ≤
      Nat.card (Subgroup.center SL(2, ℤ)) := Nat.card_le_card_of_injective _ hinj
  -- `h2` is used as a hypothesis, never rewritten: `rw [← card_center]` would abstract the `2`
  -- in `SL(2, ℤ)` too, since that numeral is the matrix dimension
  exact ⟨Nat.card_pos, by omega⟩

/-- **The complementary case**: the factor is `1` exactly when `-I ∉ Γ`, i.e. when the matrix and
projective stabiliser orders agree. -/
theorem card_center_subgroupOf_eq_one_iff (Γ : Subgroup SL(2, ℤ)) :
    Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) = 1 ↔ (-1 : SL(2, ℤ)) ∉ Γ := by
  rw [Subgroup.card_eq_one]
  constructor
  · intro h hneg
    -- `-I` would be a second element, so triviality forces it out of `Γ`
    have hx := (Subgroup.eq_bot_iff_forall _).mp h (⟨-1, hneg⟩ : Γ)
      (Subgroup.mem_subgroupOf.mpr neg_one_mem_center)
    exact neg_one_ne_one (by simpa using Subtype.ext_iff.mp hx)
  · intro hneg
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx ↦ ?_
    rcases eq_one_or_neg_one_of_mem_center (Subgroup.mem_subgroupOf.mp hx) with hx1 | hx1
    · exact Subtype.ext hx1
    · exact absurd (show (-1 : SL(2, ℤ)) ∈ Γ from hx1 ▸ x.2) hneg

/-- **The `±I` factor is `2` exactly when `-I ∈ Γ`.** The part of the centre that `Γ` contains is
`{I}` or `{±I}` according to whether `Γ` contains `-I`, so the factor in the splitting
`card_stabilizer_eq_card_center_mul_card_stabilizer_psl` is decided by that single membership. -/
theorem card_center_subgroupOf_eq_two_iff (Γ : Subgroup SL(2, ℤ)) :
    Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) = 2 ↔ (-1 : SL(2, ℤ)) ∈ Γ := by
  obtain ⟨hpos, hle⟩ := card_center_subgroupOf_le_two Γ
  constructor
  · intro h
    by_contra hneg
    have h1 := (card_center_subgroupOf_eq_one_iff Γ).mpr hneg
    omega
  · intro hneg
    have h1 : Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) ≠ 1 := fun h ↦
      (card_center_subgroupOf_eq_one_iff Γ).mp h hneg
    omega

/-- **The `±I` factor is `1` or `2`.** The unindexed corollary of
`card_center_subgroupOf_eq_two_iff`, for a consumer that needs only the bound — to know that the
projective order divides the matrix one, say — and not the membership. -/
theorem card_center_subgroupOf_eq_one_or_two (Γ : Subgroup SL(2, ℤ)) :
    Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) = 1 ∨
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) = 2 := by
  by_cases h : (-1 : SL(2, ℤ)) ∈ Γ
  · exact Or.inr ((card_center_subgroupOf_eq_two_iff Γ).mpr h)
  · exact Or.inl ((card_center_subgroupOf_eq_one_iff Γ).mpr h)

/-- **The `SL(2, ℤ)`-stabiliser order is twice the `PSL(2, ℤ)` one.** The two differ exactly by
the centre `±1`, which acts trivially on `ℍ`, so every projective stabiliser is the matrix one
halved — the passage from the counts `4`, `6`, `2` to the elliptic orders `e_P`. -/
theorem card_stabilizer_eq_two_mul_card_stabilizer_psl (z : ℍ) :
    Nat.card (stabilizer SL(2, ℤ) z) = 2 * Nat.card (stabilizer PSL(2, ℤ) z) := by
  rw [TauCeti.card_stabilizer_eq_card_subgroup_mul_card_stabilizer_quotient _ z
    fun g ↦ UpperHalfPlane.pslMk_smul g z, card_center]

-- Neither elliptic order below is `@[simp]`, tested: `MulAction.mem_stabilizer_iff` rewrites
-- `Nat.card (stabilizer G z)` into a `Nat.card` of a subtype underneath, so the left-hand side is
-- not in simp-normal form and `simpNF` rejects the attribute — the same reason recorded above for
-- the `SL(2, ℤ)` counts.

/-- **The elliptic order at `i` is `e_i = 2`** — the order of the `PSL(2, ℤ)`-stabiliser, not the
weight: the valence formula weights that orbit by the reciprocal `1 / e_i = 1 / 2`. -/
theorem card_stabilizer_psl_I : Nat.card (stabilizer PSL(2, ℤ) I) = 2 := by
  have h := card_stabilizer_eq_two_mul_card_stabilizer_psl I
  rw [card_stabilizer_I] at h
  omega

/-- **The elliptic order at `ρ` is `e_ρ = 3`** — again the stabiliser order; the valence formula
weights that orbit by `1 / e_ρ = 1 / 3`. -/
theorem card_stabilizer_psl_ρ : Nat.card (stabilizer PSL(2, ℤ) ρ) = 3 := by
  have h := card_stabilizer_eq_two_mul_card_stabilizer_psl ρ
  rw [card_stabilizer_ρ] at h
  omega

/-- **Every non-elliptic orbit has `e_P = 1`**: away from the orbits of `i` and `ρ`, the
`PSL(2, ℤ)`-action on `ℍ` is free. -/
theorem card_stabilizer_psl_eq_one_of_orbit_ne_I_of_orbit_ne_ρ (z : ℍ)
    (hI : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' I)
    (hρ : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' ρ) :
    Nat.card (stabilizer PSL(2, ℤ) z) = 1 := by
  have h := card_stabilizer_eq_two_mul_card_stabilizer_psl z
  rw [card_stabilizer_eq_two_of_orbit_ne_I_of_orbit_ne_ρ z hI hρ] at h
  omega

end ModularGroup

end TauCeti

end
