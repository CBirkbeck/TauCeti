/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FixedSubmodule
import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# Dimensions of common fixed submodules

This file computes the dimension of the common fixed submodule of a finite family of commuting
idempotent endomorphisms when each new fixed-point condition has an explicitly equivalent
complementary eigenspace.

## Main results

* `TauCeti.two_mul_finrank_fixedSubmodule_of_isIdempotentElem`: an idempotent whose fixed vectors
  and kernel are exchanged by maps that are mutually inverse there has a fixed submodule of half
  the dimension.
* `TauCeti.finrank_fixedSubmodule_restrict_eq_finrank_iInf_insert`: inside a common fixed
  submodule, the fixed submodule of the restriction of one more endomorphism has the dimension of
  the enlarged common fixed submodule.
* `TauCeti.two_mul_finrank_iInf_fixedSubmodule_insert`: adjoining one such idempotent halves the
  common fixed-space dimension.
* `TauCeti.pow_card_mul_finrank_iInf_fixedSubmodule`: iterating the construction multiplies the
  common fixed-space dimension by a power of two.
-/

public section

open Module

namespace TauCeti

/-- If `u` maps the fixed vectors of an idempotent endomorphism `q` of a finite-dimensional space
into the kernel of `q`, `v` maps the kernel into the fixed vectors, and these two restrictions are
mutually inverse, then the fixed submodule of `q` has half the dimension of the space. -/
theorem two_mul_finrank_fixedSubmodule_of_isIdempotentElem {K W : Type*} [DivisionRing K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {q : Module.End K W}
    (hq : IsIdempotentElem q) (u v : Module.End K W) (hu0 : ∀ x, q x = x → q (u x) = 0)
    (hv1 : ∀ x, q x = 0 → q (v x) = v x) (hvu : ∀ x, q x = x → v (u x) = x)
    (huv : ∀ x, q x = 0 → u (v x) = x) :
    2 * finrank K q.fixedSubmodule = finrank K W := by
  have hf {x} := LinearMap.mem_fixedSubmodule_iff (f := q) (v := x)
  -- For an idempotent, the range is exactly the submodule of fixed vectors.
  have hr : LinearMap.range q = q.fixedSubmodule := by
    ext x
    rw [LinearMap.IsIdempotentElem.mem_range_iff hq, hf]
  -- `u` and `v` restrict to mutually inverse maps between the fixed vectors and the kernel of `q`.
  let e : q.fixedSubmodule ≃ₗ[K] LinearMap.ker q := .ofLinearMap
    (u.restrict fun x hx => LinearMap.mem_ker.mpr (hu0 x (hf.mp hx)))
    (v.restrict fun x hx => hf.mpr (hv1 x (LinearMap.mem_ker.mp hx)))
    (by ext x; simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.coe_restrict_apply]
      using huv x (LinearMap.mem_ker.mp x.2))
    (by ext x; simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.coe_restrict_apply]
      using hvu x (hf.mp x.2))
  -- Rank-nullity for `q`, with its kernel replaced by the isomorphic fixed submodule.
  rw [two_mul, ← q.finrank_range_add_finrank_ker, hr, e.finrank_eq]

/-- Let `S` be the common fixed submodule of the endomorphisms `p i`, `i ∈ s`, and suppose `p a`
maps `S` into itself. Then the fixed submodule of the restriction of `p a` to `S` has the same
dimension as the common fixed submodule of the `p i`, `i ∈ insert a s`. The invariance hypothesis
holds, for instance, when `p a` commutes with every `p i`, `i ∈ s`. -/
theorem finrank_fixedSubmodule_restrict_eq_finrank_iInf_insert {K V ι : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V] [DecidableEq ι] {p : ι → Module.End K V} {s : Finset ι} {a : ι}
    (hpS : ∀ x ∈ ⨅ i ∈ s, (p i).fixedSubmodule, p a x ∈ ⨅ i ∈ s, (p i).fixedSubmodule) :
    finrank K ((p a).restrict hpS).fixedSubmodule =
      finrank K ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V) := by
  -- Inside the old common fixed space, the new one is the fixed space of the restriction.
  have hfix : ((p a).restrict hpS).fixedSubmodule =
      (⨅ i ∈ insert a s, (p i).fixedSubmodule).comap (⨅ i ∈ s, (p i).fixedSubmodule).subtype := by
    ext x
    rw [Submodule.mem_comap, Finset.iInf_insert, Submodule.mem_inf,
      LinearMap.mem_fixedSubmodule_iff, LinearMap.mem_fixedSubmodule_iff, Subtype.ext_iff,
      LinearMap.coe_restrict_apply, Submodule.coe_subtype, and_iff_left x.2]
  rw [hfix]
  exact (Submodule.comapSubtypeEquivOfLe (biInf_mono fun _ => Finset.mem_insert_of_mem)).finrank_eq

/-- If two endomorphisms exchange the fixed and zero eigenspaces of an idempotent inside the
common fixed space of a commuting family, adjoining that idempotent halves the dimension.

The maps `u` and `v` are stated on the ambient module so callers can supply natural operators;
the commuting hypotheses ensure that their restrictions preserve the previous common fixed
space. -/
theorem two_mul_finrank_iInf_fixedSubmodule_insert
    {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι]
    (p : ι → Module.End K V) (s : Finset ι) (a : ι)
    (hpa : IsIdempotentElem (p a))
    (hcomm : ∀ i ∈ s, Commute (p i) (p a))
    (u v : Module.End K V)
    (huS : ∀ i ∈ s, Commute (p i) u)
    (hvS : ∀ i ∈ s, Commute (p i) v)
    (hu0 : ∀ x, p a x = x → p a (u x) = 0)
    (hv1 : ∀ x, p a x = 0 → p a (v x) = v x)
    (hvu : ∀ x, p a x = x → v (u x) = x)
    (huv : ∀ x, p a x = 0 → u (v x) = x) :
    2 * finrank K ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V) =
      finrank K ((⨅ i ∈ s, (p i).fixedSubmodule) : Submodule K V) := by
  let S : Submodule K V := ⨅ i ∈ s, (p i).fixedSubmodule
  have hS {f : Module.End K V} (hf : ∀ i ∈ s, Commute (p i) f) : ∀ x ∈ S, f x ∈ S :=
    LinearMap.iInf_invariant f fun i => LinearMap.iInf_invariant f fun hi _ =>
      apply_mem_fixedSubmodule_of_commute (hf i hi)
  let q : Module.End K S := (p a).restrict (hS hcomm)
  have hq : IsIdempotentElem q := LinearMap.ext fun x => Subtype.ext <| by
    simpa only [q, Module.End.mul_apply, LinearMap.coe_restrict_apply] using
      LinearMap.congr_fun hpa.eq (x : V)
  rw [← finrank_fixedSubmodule_restrict_eq_finrank_iInf_insert (hS hcomm),
    two_mul_finrank_fixedSubmodule_of_isIdempotentElem hq (u.restrict (hS huS))
      (v.restrict (hS hvS))]
  -- The four exchange hypotheses restrict from `V` to `S`.
  all_goals
    intro x hx
    simp only [q, Subtype.ext_iff, LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] at hx ⊢
  exacts [hu0 _ hx, hv1 _ hx, hvu _ hx, huv _ hx]

/-- A finite family of commuting idempotent endomorphisms has common fixed-space dimension
`2 ^ (-|t|)` times the ambient dimension when each idempotent's fixed and zero pieces are
exchanged by inverse endomorphisms that commute with the other idempotents. -/
theorem pow_card_mul_finrank_iInf_fixedSubmodule
    {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (p : ι → Module.End K V) (t : Finset ι)
    (hp : ∀ a ∈ t, IsIdempotentElem (p a))
    (hcomm : (t : Set ι).Pairwise fun a b => Commute (p a) (p b))
    (u v : ι → Module.End K V)
    (huS : ∀ a ∈ t, ∀ i ∈ t, i ≠ a → Commute (p i) (u a))
    (hvS : ∀ a ∈ t, ∀ i ∈ t, i ≠ a → Commute (p i) (v a))
    (hu0 : ∀ a ∈ t, ∀ x, p a x = x → p a (u a x) = 0)
    (hv1 : ∀ a ∈ t, ∀ x, p a x = 0 → p a (v a x) = v a x)
    (hvu : ∀ a ∈ t, ∀ x, p a x = x → v a (u a x) = x)
    (huv : ∀ a ∈ t, ∀ x, p a x = 0 → u a (v a x) = x) :
    2 ^ t.card * finrank K ((⨅ i ∈ t, (p i).fixedSubmodule) : Submodule K V) =
      finrank K V := by
  classical
  induction t using Finset.induction with
  | empty =>
      have hempty : (⨅ i ∈ (∅ : Finset ι), (p i).fixedSubmodule) =
          (⊤ : Submodule K V) := by
        ext x
        simp
      rw [hempty]
      simp
  | @insert a s ha ih =>
      have hrec : 2 * finrank K
          ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V) =
          finrank K ((⨅ i ∈ s, (p i).fixedSubmodule) : Submodule K V) :=
        two_mul_finrank_iInf_fixedSubmodule_insert p s a (hp a (by simp))
          (fun i hi => hcomm (by simp [hi]) (by simp) (by
            exact fun hia => ha (hia ▸ hi))) (u a) (v a)
          (fun i hi => huS a (by simp) i (by simp [hi]) (by
            exact fun hia => ha (hia ▸ hi)))
          (fun i hi => hvS a (by simp) i (by simp [hi]) (by
            exact fun hia => ha (hia ▸ hi)))
          (hu0 a (by simp)) (hv1 a (by simp)) (hvu a (by simp)) (huv a (by simp))
      have ih' := ih (fun b hb => hp b (by simp [hb]))
        (hcomm.mono (by simp))
        (fun b hb i hi hne => huS b (by simp [hb]) i (by simp [hi]) hne)
        (fun b hb i hi hne => hvS b (by simp [hb]) i (by simp [hi]) hne)
        (fun b hb => hu0 b (by simp [hb]))
        (fun b hb => hv1 b (by simp [hb]))
        (fun b hb => hvu b (by simp [hb]))
        (fun b hb => huv b (by simp [hb]))
      rw [Finset.card_insert_of_notMem ha, pow_succ]
      calc
        2 ^ s.card * 2 * finrank K
            ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V) =
            2 ^ s.card * (2 * finrank K
              ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V)) :=
          Nat.mul_assoc _ _ _
        _ = 2 ^ s.card * finrank K
            ((⨅ i ∈ s, (p i).fixedSubmodule) : Submodule K V) := by rw [hrec]
        _ = finrank K V := ih'

end TauCeti
