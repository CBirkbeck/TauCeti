/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Length

/-!
# General facts about the length of a module

Mathlib defines `Module.length R M` as the Krull dimension of the lattice of submodules and
proves that it is additive in short exact sequences. This file adds the facts about it that a
length-counting argument needs but Mathlib does not yet have: monotonicity in the submodule
quotiented by, additivity along a filtration, the length of an image, and the fact that
finitely generated submodules already see the whole length.

The last of these is the load-bearing one. `Module.length` is a supremum over strictly
increasing chains, and any *finite* chain — in particular any one witnessing a finite lower
bound on the length — is realised inside a finitely generated submodule, spanned by one element
taken from each of its steps. So a uniform bound on finitely generated submodules is a bound on
the module.

Multiplication by a ring element `a` on a module `M` is written throughout as
`LinearMap.range (LinearMap.lsmul A M a)`, which is the submodule `aM`.

## Main results

* `TauCeti.length_quotient_le_of_le`: `M ⧸ Q` is no longer than `M ⧸ P` when `P ≤ Q`.
* `TauCeti.length_quotient_eq_length_map_add_length_quotient_sup`: additivity along a filtration.
* `TauCeti.length_map_mkQ`: the length of the image of `N` in `M ⧸ P`.
* `TauCeti.length_le_of_forall_fg`: a bound on all finitely generated submodules bounds the
  length.
* `TauCeti.length_quotient_lsmul_le_of_forall_fg`: the same reduction for `M ⧸ aM`.
-/

public section

namespace TauCeti

section Ring

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- Quotienting by a larger submodule cannot increase length. -/
theorem length_quotient_le_of_le {P Q : Submodule A M} (h : P ≤ Q) :
    Module.length A (M ⧸ Q) ≤ Module.length A (M ⧸ P) := by
  rw [Module.length_quotient, Module.length_quotient]
  exact Order.coheight_anti h

/-- **Filtration additivity.** The image of `N` in `M ⧸ P` and the further quotient
`M ⧸ (P ⊔ N)` account between them for the whole of `M ⧸ P`. -/
theorem length_quotient_eq_length_map_add_length_quotient_sup (N P : Submodule A M) :
    Module.length A (M ⧸ P) = Module.length A (N.map P.mkQ) + Module.length A (M ⧸ (P ⊔ N)) := by
  rw [← (Submodule.quotientQuotientEquivQuotientSup P N).length_eq]
  exact Module.length_eq_add_of_exact (N.map P.mkQ).subtype (N.map P.mkQ).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)

/-- The image of `N` in `M ⧸ P` has the length of `N ⧸ (N ⊓ P)`, for any `P`; in particular no
`P ≤ N` is needed. -/
theorem length_map_mkQ (N P : Submodule A M) :
    Module.length A (N.map P.mkQ) = Module.length A (↥N ⧸ Submodule.comap N.subtype P) := by
  have hker : LinearMap.ker (P.mkQ ∘ₗ N.subtype) = Submodule.comap N.subtype P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hran : LinearMap.range (P.mkQ ∘ₗ N.subtype) = N.map P.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hran, ← hker]
  exact ((LinearMap.quotKerEquivRange (P.mkQ ∘ₗ N.subtype)).length_eq).symm

/-- **Length is detected by finitely generated submodules.** -/
theorem length_le_of_forall_fg {c : ℕ∞} (h : ∀ N : Submodule A M, N.FG → Module.length A N ≤ c) :
    Module.length A M ≤ c := by
  rcases eq_or_ne c ⊤ with rfl | hc
  · exact le_top
  lift c to ℕ using hc
  by_contra hlt
  rw [not_le] at hlt
  -- A chain one step longer than `c` exists in the submodule lattice.
  have hstep : ((c + 1 : ℕ) : ℕ∞) ≤ Module.length A M := by
    exact_mod_cast Order.add_one_le_of_lt hlt
  have hkd : ((c + 1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (Submodule A M) := by
    rw [← Module.coe_length]; exact_mod_cast hstep
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hkd
  -- Pick a witness for each strict step, and span them: the chain survives inside that span.
  have hx : ∀ i : Fin l.length, ∃ x : M, x ∈ l i.succ ∧ x ∉ l i.castSucc := fun i =>
    SetLike.exists_of_lt (l.strictMono (Fin.castSucc_lt_succ : i.castSucc < i.succ))
  choose x hx1 hx2 using hx
  set N : Submodule A M := Submodule.span A (Set.range x) with hN
  have hxN : ∀ i, x i ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hmono : StrictMono (fun i => Submodule.comap N.subtype (l i)) :=
    Fin.strictMono_iff_lt_succ.mpr fun i => by
      refine lt_of_le_of_ne (Submodule.comap_mono
        (l.strictMono (Fin.castSucc_lt_succ : i.castSucc < i.succ)).le) ?_
      intro hEq
      refine hx2 i ?_
      have hmem : (⟨x i, hxN i⟩ : N) ∈ Submodule.comap N.subtype (l i.castSucc) := by
        rw [hEq]; exact hx1 i
      simpa using hmem
  have hq : ((l.length : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (Submodule A N) :=
    Order.LTSeries.length_le_krullDim
      (LTSeries.mk l.length (fun i => Submodule.comap N.subtype (l i)) hmono)
  rw [← Module.coe_length, hl] at hq
  have hfin := h N (Submodule.fg_span (Set.finite_range x))
  have habs : ((c + 1 : ℕ) : ℕ∞) ≤ ((c : ℕ) : ℕ∞) := le_trans (by exact_mod_cast hq) hfin
  have : c + 1 ≤ c := by exact_mod_cast habs
  omega

end Ring

section CommRing

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- For a submodule `N`, the elements of `N` lying in `aN` computed in the ambient module are
exactly the elements of `aN` computed in `N`. -/
@[simp]
theorem comap_subtype_map_lsmul (N : Submodule A M) (a : A) :
    Submodule.comap N.subtype (N.map (LinearMap.lsmul A M a))
      = LinearMap.range (LinearMap.lsmul A ↥N a) := by
  ext y
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_map,
    LinearMap.mem_range, LinearMap.lsmul_apply]
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(z : M), z.2, rfl⟩

/-- A linear equivalence identifies `M ⧸ aM` with `M' ⧸ aM'`. -/
theorem length_quotient_lsmul_congr {M' : Type*} [AddCommGroup M'] [Module A M']
    (e : M ≃ₗ[A] M') (a : A) : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a))
      = Module.length A (M' ⧸ LinearMap.range (LinearMap.lsmul A M' a)) := by
  refine (Submodule.Quotient.equiv _ _ e ?_).length_eq
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.lsmul_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    exact ⟨e w, by simp⟩
  · rintro ⟨w, rfl⟩
    exact ⟨a • e.symm w, ⟨e.symm w, rfl⟩, by simp⟩

/-- **Reduction of the length of `M ⧸ aM` to finitely generated submodules.** -/
theorem length_quotient_lsmul_le_of_forall_fg {a : A} {c : ℕ∞} (h : ∀ N : Submodule A M, N.FG →
      Module.length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N a)) ≤ c) :
    Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a)) ≤ c := by
  set P : Submodule A M := LinearMap.range (LinearMap.lsmul A M a)
  refine length_le_of_forall_fg fun Q hQ => ?_
  -- A finitely generated submodule of `M ⧸ aM` is the image of a finitely generated `N ≤ M`.
  obtain ⟨s, hs⟩ := hQ
  choose g hg using Submodule.mkQ_surjective P
  set N : Submodule A M := Submodule.span A (g '' (s : Set (M ⧸ P))) with hN
  have hNfg : N.FG := Submodule.fg_span (s.finite_toSet.image _)
  have hQeq : Q = N.map P.mkQ := by
    rw [hN, Submodule.map_span, ← hs, ← Set.image_comp]
    congr 1
    simp [hg]
  have hle : LinearMap.range (LinearMap.lsmul A ↥N a) ≤ Submodule.comap N.subtype P := by
    rintro y ⟨z, rfl⟩
    exact ⟨(z : M), rfl⟩
  calc Module.length A ↥Q = Module.length A ↥(N.map P.mkQ) := by rw [hQeq]
    _ = Module.length A (↥N ⧸ Submodule.comap N.subtype P) := length_map_mkQ N P
    _ ≤ Module.length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N a)) :=
        length_quotient_le_of_le hle
    _ ≤ c := h N hNfg

end CommRing

end TauCeti
