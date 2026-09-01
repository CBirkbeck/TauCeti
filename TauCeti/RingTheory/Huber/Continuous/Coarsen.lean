/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Continuous.OfCofinal
public import TauCeti.RingTheory.Valuation.Coarsen
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Continuity of a vertical generization

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Remark 7.11(2).**

A vertical generization `v/H` of a continuous valuation on a Huber ring is again continuous.
Wedhorn states the hypothesis as `H ⊊ Γ_v`: the convex subgroup is proper **in the value group**,
not in the ambient codomain. That is why the coarsening here is applied to `v.restrict`, which is
the presentation of `v` on its own value group; `H ≠ ⊤` is then literally Wedhorn's properness.

Properness is not decoration. If `H` were all of `Γ_v` the coarsening would take only the values
`0` and `1`, so `{a | w a < w b}` would be the support of `v`, and continuity would force that
support to be open — which it need not be.

## What the argument needs

Continuity is rebuilt from Wedhorn Remark 7.11(1), the cofinal-value criterion, in the form
`TauCeti.Huber.PairOfDefinition.isContinuous_of_forall_cofinalValue`. Two things have to survive
the coarsening, and each is one step:

* the bound `v a ≤ 1` on an ideal of definition, which is monotonicity of the coarsening map;
* cofinality of `v a` there, which is Wedhorn Corollary 1.21 — the statement carried here by
  `TauCeti.IsCofinalElement.quotientMk`.

Only the second uses properness, and it uses it exactly once: a monotone map gives `≤`, so a
witness `d ∉ H` with `1 < d` is what turns that into the strict inequality cofinality asks for.
The target is shrunk by `d⁻¹` before `v`'s own cofinality is invoked, and the resulting slack is
what survives as strictness downstairs.

## Main results

* `Valuation.IsContinuous.coarsenByUnits_restrict`: the coarsening of a continuous valuation by a
  proper convex subgroup of its value group is continuous.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.11 and Corollary 1.21.

AINTLIB's `coarsen_maxAvoid_isContinuous_mulArchimedean` is *not* the source of this proof and is
not a specialization of it: it fixes `H` to be `maxAvoid g₀`, carries a cofinality hypothesis on
`g₀`, bundles a `MulArchimedean` conclusion, and is proved against a definition of continuity
quantifying over the whole codomain rather than over attained values. Its direct sublevel-set
argument does not transfer to this statement.
-/

public section

namespace Valuation

open TauCeti TauCeti.Huber MonoidWithZeroHom

variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Wedhorn Remark 7.11(2).** A vertical generization of a continuous valuation by a proper
convex subgroup of its value group is again continuous.

The coarsening is taken on `v.restrict` rather than on `v`, so that `H ≠ ⊤` is properness in the
value group, which is the hypothesis Wedhorn states. Properness enters only through the witness
`d ∉ H` with `1 < d`: coarsening is monotone but not strictly so, and shrinking the target by
`d⁻¹` is what recovers the strict inequality that cofinality requires. -/
theorem IsContinuous.coarsenByUnits_restrict [IsTopologicalRing A] [IsHuberRing A]
    [ContinuousConstSMul Aᵐᵒᵖ A] {v : Valuation A Γ₀} (hv : v.IsContinuous)
    {H : ConvexSubgroup (ValueGroup₀ (.ofClass v))ˣ} (hH : H ≠ ⊤) :
    (v.restrict.coarsenByUnits H).IsContinuous := by
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  obtain ⟨s, hs⟩ := P.fg_idealOfDefinition
  have hv' : v.restrict.IsContinuous := (v.isEquiv_restrict).isContinuous_iff.mp hv
  obtain ⟨x, -, hxH⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hH)
  have hx1 : x ≠ 1 := fun h ↦ hxH (h ▸ one_mem H)
  obtain ⟨d, hd1, hdH⟩ : ∃ d : (ValueGroup₀ (.ofClass v))ˣ, 1 < d ∧ d ∉ H := by
    rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · exact ⟨x⁻¹, by simpa using hlt, fun hmem ↦ hxH (by simpa using inv_mem hmem)⟩
    · exact ⟨x, hgt, hxH⟩
  have hdq : 1 < QuotientGroup.mk' H.toSubgroup d := by
    have h := H.quotientMk_lt_one_of_notMem (a := d⁻¹) (by simpa using hd1.le)
      (fun hmem ↦ hdH (by simpa using inv_mem hmem))
    simpa using h
  refine P.isContinuous_of_forall_cofinalValue _ hs ?_ ?_
  · intro a ha
    rw [coarsenByUnits_apply, ← map_one (coarsenMapOfValueGroup H)]
    exact coarsenMapOfValueGroup_monotone H
      (hv'.lt_one_of_isTopologicallyNilpotent
        (P.isTopologicallyNilpotent_of_mem_idealOfDefinition ha)).le
  · intro t ht
    have hnil := P.isTopologicallyNilpotent_of_mem_idealOfDefinition (hs ▸ Ideal.subset_span ht)
    have hcof : CofinalValue v (t : A) := hv.cofinalValue_of_isTopologicallyNilpotent hnil
    rw [cofinalValue_iff]
    intro γ hγ
    obtain ⟨r, q, hr, hq, hrq⟩ :=
      (v.restrict.coarsenByUnits H).exists_div_eq_of_unit (Units.mk0 γ hγ.ne')
    simp only [Units.val_mk0] at hrq
    have hrv : v.restrict r ≠ 0 := fun h ↦ by
      rw [coarsenByUnits_apply, h, map_zero] at hr; exact lt_irrefl 0 hr
    have hqv : v.restrict q ≠ 0 := fun h ↦ by
      rw [coarsenByUnits_apply, h, map_zero] at hq; exact lt_irrefl 0 hq
    obtain ⟨n, hn⟩ := cofinalValue_iff.mp hcof
      (v.restrict r / v.restrict q * (d : ValueGroup₀ (.ofClass v))⁻¹)
      (by simp [zero_lt_iff, hrv, hqv, Units.ne_zero d])
    refine ⟨n, ?_⟩
    have hemb : ValueGroup₀.embedding γ =
        (v.restrict.coarsenByUnits H) r / (v.restrict.coarsenByUnits H) q := by
      rw [← hrq, map_div₀, Valuation.embedding_restrict, Valuation.embedding_restrict]
    rw [← map_pow, Valuation.restrict_lt_iff_lt_embedding, hemb, coarsenByUnits_apply,
      coarsenByUnits_apply, coarsenByUnits_apply, map_pow, ← map_div₀]
    calc coarsenMapOfValueGroup H (v.restrict ↑t ^ n)
        ≤ coarsenMapOfValueGroup H
            (v.restrict r / v.restrict q * (d : ValueGroup₀ (.ofClass v))⁻¹) :=
          coarsenMapOfValueGroup_monotone H hn.le
      _ < coarsenMapOfValueGroup H (v.restrict r / v.restrict q) := by
          rw [map_mul, map_inv₀, coarsenMapOfValueGroup_apply_coe]
          refine mul_lt_of_lt_one_right ?_ ?_
          · refine zero_lt_iff.mpr ?_
            rw [ne_eq, map_eq_zero, div_eq_zero_iff]
            push Not
            exact ⟨hrv, hqv⟩
          · rw [← WithZero.coe_inv, WithZero.coe_lt_one]
            simpa using hdq

end Valuation

end
