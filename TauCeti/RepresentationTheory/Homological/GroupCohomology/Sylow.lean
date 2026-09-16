/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction

/-!
# Torsion of group cohomology and restriction to Sylow subgroups

For a finite group `G`, the composite `Cor ∘ Res : Hⁿ(G, A) ⟶ Hⁿ(S, A) ⟶ Hⁿ(G, A)` is
multiplication by the index `[G : S]`. Taking `S` trivial shows that `Hⁿ(G, A)` is killed by the
order of `G` for `n ≥ 1`; taking `S` a Sylow `p`-subgroup shows that restriction to `S` is
injective on the `p`-primary part of `Hⁿ(G, A)`, because `[G : S]` is prime to `p`. Consequently
`Hⁿ(G, A)` vanishes as soon as `Hⁿ(P, A)` vanishes for a Sylow `p`-subgroup `P` of every prime
`p`, which is the reduction step of Tate's cohomological triviality criterion.

## Main statements

* `groupCohomology.card_nsmul_eq_zero`: `Nat.card G • x = 0` for `x ∈ Hⁿ⁺¹(G, A)`.
* `groupCohomology.eq_zero_of_map_sylow_eq_zero`: an element of `Hⁿ⁺¹(G, A)` killed by a power of
  `p` and by restriction to a Sylow `p`-subgroup is zero.
* `groupCohomology.isZero_of_forall_sylow`: `Hⁿ⁺¹(G, A) = 0` if `Hⁿ⁺¹(P, A) = 0` for a Sylow
  `p`-subgroup `P` of every prime `p`.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, Corollaries 1.31 and 1.33 and Theorem 3.10.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G) (n : ℕ)

/-- Positive-degree cohomology of a finite group is killed by the order of the group: the
composite `Cor ∘ Res` through the trivial subgroup is multiplication by `Nat.card G` and factors
through the vanishing cohomology of the trivial group (Milne II 1.31). -/
theorem card_nsmul_eq_zero (x : groupCohomology A (n + 1)) : Nat.card G • x = 0 := by
  have h := congrArg (fun f ↦ f.hom x)
    (TauCeti.groupCohomology.map_subtype_id_comp_corestriction (⊥ : Subgroup G) A (n + 1))
  have hz : (map (⊥ : Subgroup G).subtype (𝟙 (res (⊥ : Subgroup G).subtype A)) (n + 1)).hom x = 0 :=
    have := ModuleCat.subsingleton_of_isZero
      (isZero_groupCohomology_succ_of_subsingleton (res (⊥ : Subgroup G).subtype A) n)
    Subsingleton.elim _ _
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero, Subgroup.index_bot,
    ModuleCat.hom_nsmul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply] at h
  exact h.symm

/-- **Restriction to a Sylow `p`-subgroup is injective on the `p`-primary part** (Milne II 1.33):
an element of `Hⁿ⁺¹(G, A)` killed by a power of `p` whose restriction to a Sylow `p`-subgroup `P`
vanishes is zero, because `Cor ∘ Res` is multiplication by the index of `P`, which is prime to
`p`. -/
theorem eq_zero_of_map_sylow_eq_zero (p : ℕ) [Fact p.Prime] (P : Sylow p G)
    {x : groupCohomology A (n + 1)} {j : ℕ} (hx : p ^ j • x = 0)
    (h : map (P : Subgroup G).subtype (𝟙 (res (P : Subgroup G).subtype A)) (n + 1) x = 0) :
    x = 0 := by
  have hindex : (P : Subgroup G).index • x = 0 := by
    have h' := congrArg (fun f ↦ f.hom x)
      (TauCeti.groupCohomology.map_subtype_id_comp_corestriction (P : Subgroup G) A (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, h, map_zero, ModuleCat.hom_nsmul,
      ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply] at h'
    exact h'.symm
  have hcop : (p ^ j).Coprime (P : Subgroup G).index :=
    Nat.Coprime.pow_left j
      ((Nat.Prime.coprime_iff_not_dvd ‹Fact p.Prime›.out).2 (Sylow.not_dvd_index P))
  exact AddMonoid.addOrderOf_eq_one_iff.1 <| Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left (addOrderOf_dvd_of_nsmul_eq_zero hx) hcop)
    (addOrderOf_dvd_of_nsmul_eq_zero hindex)

/-- **The Sylow reduction of Tate's triviality criterion** (Milne II 3.10, last paragraph): if
`Hⁿ⁺¹(P, A) = 0` for a Sylow `p`-subgroup `P` of every prime `p`, then `Hⁿ⁺¹(G, A) = 0`. The
proof peels the primes off the order of `G`: an element killed by `p ^ m * a` with `p ∤ a` has
`a • x` killed by `p ^ m` and by restriction to a Sylow `p`-subgroup, hence `a • x = 0`. -/
theorem isZero_of_forall_sylow
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      IsZero (groupCohomology (res (P : Subgroup G).subtype A) (n + 1))) :
    IsZero (groupCohomology A (n + 1)) := by
  suffices hsub : ∀ (m : ℕ) (x : groupCohomology A (n + 1)), 0 < m → m • x = 0 → x = 0 by
    have : Subsingleton (groupCohomology A (n + 1)) :=
      subsingleton_of_forall_eq 0 fun x ↦ hsub _ x Nat.card_pos (card_nsmul_eq_zero A n x)
    exact ModuleCat.isZero_of_subsingleton _
  intro m
  induction m using Nat.recOnPrimePow with
  | zero => exact fun _ h0 _ ↦ absurd h0 (lt_irrefl 0)
  | one => exact fun x _ hx ↦ by simpa using hx
  | prime_pow_mul a p m hp hpa hm ih =>
    intro x hpos hx
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
    have hres : map (P : Subgroup G).subtype (𝟙 (res (P : Subgroup G).subtype A)) (n + 1)
        (a • x) = 0 :=
      have := ModuleCat.subsingleton_of_isZero (h p P)
      Subsingleton.elim _ _
    have hax : a • x = 0 :=
      eq_zero_of_map_sylow_eq_zero A n p P (j := m) (by rw [← mul_smul, hx]) hres
    exact ih x (Nat.pos_of_mul_pos_left hpos) hax

end groupCohomology
