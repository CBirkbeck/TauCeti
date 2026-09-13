module
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-! # Route B -/
public section
namespace Probe
open Subgroup

variable {G : Type*} [Group G]

theorem zpowers_self_top (g : G) :
    zpowers (⟨g, mem_zpowers g⟩ : ↥(zpowers g)) = ⊤ := by
  rw [eq_top_iff']
  rintro ⟨x, k, rfl⟩
  exact ⟨k, by ext; simp⟩

/-- the image of `g` in `⟨g⟩ ⧸ (H ∩ ⟨g⟩)` has order the relative index. -/
theorem orderOf_mk_eq_relIndex (g : G) (H : Subgroup G) :
    orderOf ((QuotientGroup.mk' (H.subgroupOf (zpowers g)))
        (⟨g, mem_zpowers g⟩ : ↥(zpowers g))) = H.relIndex (zpowers g) := by
  have hgen : zpowers ((QuotientGroup.mk' (H.subgroupOf (zpowers g)))
      (⟨g, mem_zpowers g⟩ : ↥(zpowers g))) = ⊤ := by
    rw [← MonoidHom.map_zpowers, zpowers_self_top,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [orderOf_eq_card_of_zpowers_eq_top hgen]
  rfl

/-- **The relative index is the least positive exponent landing in `H`.** -/
theorem isLeast_pow_mem [Finite G] (g : G) (H : Subgroup G) :
    IsLeast {n : ℕ | 0 < n ∧ g ^ n ∈ H} (H.relIndex (zpowers g)) := by
  set d := H.relIndex (zpowers g) with hd
  have hord := orderOf_mk_eq_relIndex g H
  have key : ∀ n : ℕ, g ^ n ∈ H ↔ d ∣ n := fun n ↦ by
    rw [hd, ← hord, orderOf_dvd_iff_pow_eq_one, ← map_pow,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simp
  constructor
  · refine ⟨?_, (key d).2 dvd_rfl⟩
    rw [hd, ← hord]
    exact orderOf_pos _
  · rintro n ⟨hn, hmem⟩
    exact Nat.le_of_dvd hn ((key n).1 hmem)

end Probe

-- VERIFIED r827 against origin/main. 1487 jobs, 1.7s, zero sorries,
-- axioms = [propext, Classical.choice, Quot.sound].
--
-- ROUTE B WORKED, and my r825/r826 estimate of "40-60 lines of genuine group theory" was wrong:
-- the whole thing is ~30 lines. What blocked it at r826 was not difficulty but three guessed
-- lemma names. Every one of them cost a build:
--   * `zpowers_self_eq_top`      -> does not exist; the fact is true and proves in FOUR lines
--                                   (eq_top_iff' + rintro ⟨x, k, rfl⟩).
--   * `QuotientGroup.mk'_eq_one_iff` -> the real name is `QuotientGroup.eq_one_iff`, and it is
--                                   stated for the COERCION `(x : G ⧸ N)`, so it needs
--                                   `QuotientGroup.mk'_apply` to bridge from `mk'`.
--   * `MonoidHom.map_zpowers` was right but needed the hom APPLIED as `mk' N x`, not `mk x`.
--
-- "Absent from Mathlib" and "expensive to prove" are independent. At r826 I concluded the second
-- from the first and stopped.
--
-- HOME: TauCeti/GroupTheory/Index.lean (owns TauCeti's relIndex lemmas). No number theory here.
-- CONSUMER: #6241's `inertiaDeg_under_fixedField_eq_relIndex` — rewriting with isLeast_pow_mem
-- gives Chebotarev 8.2(2) in the roadmap's own words.
