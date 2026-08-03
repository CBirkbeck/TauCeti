/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Diamond operators and modular forms with character

The diamond operators `⟨d⟩` on modular and cusp forms for `Γ₁(N)`, and the nebentypus
character spaces `M_k(Γ₁(N), χ)` and `S_k(Γ₁(N), χ)` they cut out.

Since `Γ₁(N)` is normal in `Γ₀(N)` with quotient `(ZMod N)ˣ` (via the lower-right entry, the
map `CongruenceSubgroup.Gamma0Map`), slashing by any lift of `d ∈ (ZMod N)ˣ` is a well-defined
linear endomorphism of `M_k(Γ₁(N))` and of `S_k(Γ₁(N))`: the diamond operator `⟨d⟩`, packaged
as monoid homomorphisms `diamondOpHom` and `diamondOpCuspHom` into the endomorphism algebras.
The character space `modFormCharSpace k χ` (resp. `cuspFormCharSpace k χ`) is the simultaneous
`χ`-eigenspace of the diamond operators, a `Submodule` of Mathlib's `ModularForm` — not a new
bundled type — and membership in it is equivalent to the classical nebentypus transformation
law `f ∣[k] γ = χ(d_γ) • f` for `γ ∈ Γ₀(N)` (`modFormCharSpace_iff_nebentypus`).

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean`, Chris Birkbeck), realizing Layer 0 of the
ModularForms roadmap; the roadmap pins these definitions (eigenspace-in-a-`Submodule`, not a
re-founded slash action with built-in character) and their names. The Hecke pair
`(Γ₁(N), Δ₁(N))` from the same source file is Layer-2 material and is not ported here.

## Main definitions

* `CongruenceSubgroup.Gamma0MapUnits`: the lower-right entry as a homomorphism
  `Γ₀(N) →* (ZMod N)ˣ`.
* `diamondOp`/`diamondOpCusp`: the diamond operator `⟨d⟩` for `d : (ZMod N)ˣ`, a linear
  endomorphism of `ModularForm ((Gamma1 N).map (mapGL ℝ)) k` resp. `CuspForm _ k`.
* `diamondOpHom`/`diamondOpCuspHom`: the diamond operators as monoid homomorphisms into the
  endomorphism algebras.
* `modFormCharSpace`/`cuspFormCharSpace`: the nebentypus character spaces `M_k(Γ₁(N), χ)` and
  `S_k(Γ₁(N), χ)`, cut out as simultaneous diamond eigenspaces.

## Main results

* `CongruenceSubgroup.Gamma0MapUnits_surjective`: every unit of `ZMod N` is the lower-right
  entry of a matrix in `Γ₀(N)` (via strong approximation for `SL₂`).
* `modFormCharSpace_iff_nebentypus`/`cuspFormCharSpace_iff_nebentypus`: membership in the
  character space is the classical nebentypus relation `f ∣[k] g = χ(d_g) • f` for all
  `g ∈ Γ₀(N)`.

## References

* Miyake, *Modular forms*, §4.5
* Diamond–Shurman, *A first course in modular forms*, §5.1
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

variable {N : ℕ}

namespace CongruenceSubgroup

/-- Conjugation by a `Gamma0 N` element preserves `Gamma1 N`.
This is the foundation for the diamond operator `⟨d⟩` on modular forms. -/
theorem Gamma0_normalizes_Gamma1 (g : ↥(Gamma0 N)) (h : SL(2, ℤ)) (hh : h ∈ Gamma1 N) :
    (g : SL(2, ℤ)) * h * (g : SL(2, ℤ))⁻¹ ∈ Gamma1 N :=
  (Gamma1_mem _ _).mpr <| (Gamma1_to_Gamma0_mem _).mp <|
    (Gamma0Map N).normal_ker.conj_mem ⟨h, Gamma1_in_Gamma0 N hh⟩
      ((Gamma1_to_Gamma0_mem _).mpr ((Gamma1_mem _ _).mp hh)) g

/-- `(Gamma1 N).map (mapGL ℝ)` is invariant under conjugation by `Gamma0 N` elements
in `GL₂(ℝ)`. -/
theorem Gamma1_map_conjAct_eq (g : ↥(Gamma0 N)) :
    ConjAct.toConjAct (mapGL ℝ (g : SL(2, ℤ)))⁻¹ •
    (Gamma1 N).map (mapGL ℝ) = (Gamma1 N).map (mapGL ℝ) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, hσy⟩
    have hmem : (g : SL(2, ℤ))⁻¹ * σ * (g : SL(2, ℤ)) ∈ Gamma1 N := by
      simpa [inv_inv] using Gamma0_normalizes_Gamma1
        ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 N).inv_mem g.property⟩ σ hσ
    exact ⟨_, hmem, by
      simp only [map_mul, map_inv, hσy]
      group⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨(g : SL(2, ℤ)) * σ * (g : SL(2, ℤ))⁻¹,
      Gamma0_normalizes_Gamma1 g σ hσ, by simp [map_mul, map_inv]⟩

/-- Forward variant of `Gamma1_map_conjAct_eq`: `(Gamma1 N).map (mapGL ℝ)` is invariant
under conjugation by `mapGL ℝ g` (rather than its inverse). -/
theorem Gamma1_map_conjAct_eq_forward (g : ↥(Gamma0 N)) :
    ConjAct.toConjAct (mapGL ℝ (g : SL(2, ℤ))) •
    (Gamma1 N).map (mapGL ℝ) = (Gamma1 N).map (mapGL ℝ) := by
  simpa [map_inv, ConjAct.toConjAct_inv, inv_inv, inv_smul_eq_iff] using
    Gamma1_map_conjAct_eq ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 N).inv_mem g.property⟩

/-- The `Gamma0Map` lifts to a group homomorphism to `(ZMod N)ˣ`: the lower-right
entry is a unit mod `N` with inverse the upper-left entry (from `det = 1` and `N ∣ c`). -/
noncomputable def Gamma0MapUnits : ↥(Gamma0 N) →* (ZMod N)ˣ where
  toFun g := by
    set A := (g : SL(2, ℤ))
    have hc : (A 1 0 : ZMod N) = 0 := Gamma0_mem.mp g.property
    have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using A.prop
    have hunit : (A 0 0 : ZMod N) * (A 1 1 : ZMod N) = 1 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero]
        using congr_arg (Int.cast : ℤ → ZMod N) hdet
    exact Units.mk (Gamma0Map N g) (A 0 0 : ZMod N) ((mul_comm _ _).trans hunit) hunit
  map_one' := Units.ext (map_one (Gamma0Map N))
  map_mul' g₁ g₂ := Units.ext (map_mul (Gamma0Map N) g₁ g₂)

@[simp]
lemma Gamma0MapUnits_val (g : ↥(Gamma0 N)) : (Gamma0MapUnits g : ZMod N) = Gamma0Map N g := (rfl)

/-- If two `Γ₀(N)` elements have equal image under `Gamma0Map`, their ratio
`g₁ · g₂⁻¹` lies in `Γ₁(N)` (as an `SL₂(ℤ)` element). -/
lemma mul_inv_mem_Gamma1_of_Gamma0Map_eq (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    ((g₁ : SL(2, ℤ)) * (g₂ : SL(2, ℤ))⁻¹) ∈ Gamma1 N := by
  have heq_u : Gamma0MapUnits g₁ = Gamma0MapUnits g₂ := Units.ext heq
  have hker : Gamma0MapUnits (g₁ * g₂⁻¹) = 1 := by simp [map_mul, map_inv, heq_u]
  exact (Gamma1_mem _ _).mpr <| (Gamma1_to_Gamma0_mem _).mp <| congr_arg Units.val hker

/-- The diagonal matrix `!![u⁻¹, 0; 0, u]` as an element of `SL₂(ZMod N)`. -/
private def diagUnit (u : (ZMod N)ˣ) : SpecialLinearGroup (Fin 2) (ZMod N) :=
  ⟨!![(↑u⁻¹ : ZMod N), 0; 0, ↑u], by simp [det_fin_two_of]⟩

private lemma coe_diagUnit (u : (ZMod N)ˣ) :
    (diagUnit u : Matrix (Fin 2) (Fin 2) (ZMod N)) = !![(↑u⁻¹ : ZMod N), 0; 0, ↑u] := rfl

/-- `Gamma0MapUnits` is surjective: every unit `u ∈ (ZMod N)ˣ` is realized as the
lower-right entry of some `g ∈ Gamma0 N`, by strong approximation for `SL₂`. -/
theorem Gamma0MapUnits_surjective [NeZero N] :
    Function.Surjective (Gamma0MapUnits (N := N)) := fun u ↦ by
  obtain ⟨g, hg⟩ := map_intCast_zmod_surjective (diagUnit u)
  have hentry : ∀ i j, ((g i j : ℤ) : ZMod N) =
      (!![(↑u⁻¹ : ZMod N), 0; 0, ↑u] : Matrix (Fin 2) (Fin 2) (ZMod N)) i j := fun i j => by
    have h := congrArg
      (fun A : SpecialLinearGroup (Fin 2) (ZMod N) => (A : Matrix (Fin 2) (Fin 2) (ZMod N)) i j)
      hg
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
      coe_diagUnit] using h
  have h10 : ((g 1 0 : ℤ) : ZMod N) = 0 := by rw [hentry]; simp
  have h11 : ((g 1 1 : ℤ) : ZMod N) = u := by rw [hentry]; simp
  exact ⟨⟨g, Gamma0_mem.mpr h10⟩, Units.ext (by simpa [Gamma0Map] using h11)⟩

end CongruenceSubgroup

open CongruenceSubgroup

/-- The slash-action conjugation `σ` is the identity for matrices coming from
`SL₂(ℤ)`: their determinant is `1 > 0`, so the `σ` branch picks `ContinuousAlgEquiv.refl ℝ ℂ`. -/
@[simp]
lemma σ_mapGL_real_eq_refl (s : SL(2, ℤ)) :
    UpperHalfPlane.σ (mapGL ℝ s) = ContinuousAlgEquiv.refl ℝ ℂ := by
  simp [UpperHalfPlane.σ, SpecialLinearGroup.mapGL]

/-- For a function `f` invariant under `(Gamma1 N).map (mapGL ℝ)`, the slash action
`f ↦ f ∣[k] (mapGL ℝ g)` for `g ∈ Γ₀(N)` produces another `(Gamma1 N).map (mapGL ℝ)`-invariant
function. -/
lemma slash_mapGL_invariant_of_Gamma1_invariant {k : ℤ} (g : ↥(Gamma0 N))
    {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℝ), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (f ∣[k] mapGL ℝ (g : SL(2, ℤ))) ∣[k] γ = f ∣[k] mapGL ℝ (g : SL(2, ℤ)) := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  rw [← SlashAction.slash_mul, ← map_mul,
    show (g : SL(2, ℤ)) * σ = ((g : SL(2, ℤ)) * σ * (g : SL(2, ℤ))⁻¹) * (g : SL(2, ℤ)) by group,
    map_mul, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map.mpr ⟨_, Gamma0_normalizes_Gamma1 g σ hσ, rfl⟩)]

/-- For `g ∈ Γ₀(N)` and `γ ∈ GL₂(ℝ)` with `γ • ∞ = c`, a cusp `c` for
`(Gamma1 N).map (mapGL ℝ)` transports along the conjugation by `mapGL ℝ g` to a cusp at
`(mapGL ℝ g · γ) • ∞`. -/
lemma isCusp_mul_mapGL_smul_infty (g : ↥(Gamma0 N))
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ)))
    {γ : GL (Fin 2) ℝ} (hγ : γ • (OnePoint.infty : OnePoint ℝ) = c) :
    IsCusp ((mapGL ℝ (g : SL(2, ℤ)) * γ) • (OnePoint.infty : OnePoint ℝ))
      ((Gamma1 N).map (mapGL ℝ)) := by
  rw [mul_smul, hγ]
  exact Gamma1_map_conjAct_eq_forward g ▸ hc.smul (mapGL ℝ (g : SL(2, ℤ)))

/-- The diamond operator on modular forms for `Gamma1 N`, at a chosen representative: for
`g ∈ Gamma0 N`, the slash action `f ↦ f ∣[k] g` preserves
`ModularForm ((Gamma1 N).map (mapGL ℝ)) k` by the normality of `Γ₁(N)` in `Γ₀(N)`. -/
noncomputable def diamondOpAux (k : ℤ) (g : ↥(Gamma0 N)) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
      { toFun := ⇑f ∣[k] (mapGL ℝ (g : SL(2, ℤ)))
        slash_action_eq' _ hγ :=
          slash_mapGL_invariant_of_Gamma1_invariant g
            (fun _ hδ ↦ SlashInvariantFormClass.slash_action_eq f _ hδ) hγ }
      holo' := (ModularFormClass.holo f).slash k _
      bdd_at_cusps' {c} hc _ hγ := by
        rw [← SlashAction.slash_mul, ← OnePoint.isBoundedAt_infty_iff,
          ← OnePoint.IsBoundedAt.smul_iff]
        exact ModularFormClass.bdd_at_cusps f (isCusp_mul_mapGL_smul_infty g hc hγ) }
  map_add' f₁ f₂ := by
    ext z
    exact congr_fun (SlashAction.add_slash k (mapGL ℝ (g : SL(2, ℤ))) ⇑f₁ ⇑f₂) z
  map_smul' c f := by
    ext z
    -- the coercion of a bundled form slashes pointwise by definition; `change` states the
    -- unfolded form so that the slash-action lemma applies (no rewriting lemma exists here)
    change ((c • ⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z = c • _
    simp [ModularForm.smul_slash]

/-- Slash-transport for `Γ₁(N)`-invariant functions: if `f` is invariant under
`(Gamma1 N).map (mapGL ℝ)` and `Gamma0Map N g₁ = Gamma0Map N g₂`, then
`f ∣[k] g₁ = f ∣[k] g₂`. -/
lemma slash_eq_of_Gamma0Map_eq {k : ℤ} {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℝ), f ∣[k] γ = f)
    (g₁ g₂ : ↥(Gamma0 N)) (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    f ∣[k] mapGL ℝ (g₁ : SL(2, ℤ)) = f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ)) := by
  rw [show (g₁ : SL(2, ℤ)) = ((g₁ : SL(2, ℤ)) * (g₂ : SL(2, ℤ))⁻¹) * (g₂ : SL(2, ℤ)) by group,
    map_mul, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map.mpr ⟨_, mul_inv_mem_Gamma1_of_Gamma0Map_eq g₁ g₂ heq, rfl⟩)]

/-- The diamond operator depends only on the `Gamma0Map` value: if two `Gamma0 N`
elements have the same image, their diamond operators agree. -/
theorem diamondOpAux_eq_of_Gamma0Map_eq (k : ℤ) (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) : diamondOpAux k g₁ = diamondOpAux k g₂ := by
  ext f z
  exact congr_fun (slash_eq_of_Gamma0Map_eq
    (fun _ hγ ↦ SlashInvariantFormClass.slash_action_eq f _ hγ) g₁ g₂ heq) z

/-- The diamond operator `⟨d⟩` on modular forms for `Gamma1 N`, indexed by
`d : (ZMod N)ˣ`. -/
noncomputable def diamondOp [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  diamondOpAux k (Gamma0MapUnits_surjective d).choose

/-- `diamondOp` equals `diamondOpAux` on any representative with the right image. -/
theorem diamondOp_eq_diamondOpAux [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : Gamma0MapUnits g = d) : diamondOp k d = diamondOpAux k g :=
  diamondOpAux_eq_of_Gamma0Map_eq k _ g
    (by simp [← Gamma0MapUnits_val, (Gamma0MapUnits_surjective d).choose_spec, hg])

/-- The diamond operator at `1` is the identity. -/
@[simp]
theorem diamondOp_one [NeZero N] (k : ℤ) : diamondOp (N := N) k 1 = LinearMap.id := by
  rw [diamondOp_eq_diamondOpAux k 1 1 (map_one _)]
  ext f z
  -- state the unfolded slash of the coercion so `slash_one` applies
  change (⇑f ∣[k] mapGL ℝ (1 : SL(2, ℤ))) z = f z
  simp only [map_one, SlashAction.slash_one]

/-- Diamond operators compose: `⟨d₁ * d₂⟩ = ⟨d₁⟩ ∘ ⟨d₂⟩`. -/
theorem diamondOp_mul [NeZero N] (k : ℤ) (d₁ d₂ : (ZMod N)ˣ) :
    diamondOp k (d₁ * d₂) = (diamondOp k d₁).comp (diamondOp k d₂) := by
  obtain ⟨g₁, hg₁⟩ := Gamma0MapUnits_surjective (N := N) d₁
  obtain ⟨g₂, hg₂⟩ := Gamma0MapUnits_surjective (N := N) d₂
  rw [diamondOp_eq_diamondOpAux k (d₁ * d₂) (g₂ * g₁) (by simp [map_mul, hg₁, hg₂, mul_comm]),
    diamondOp_eq_diamondOpAux k d₁ g₁ hg₁, diamondOp_eq_diamondOpAux k d₂ g₂ hg₂]
  ext f z
  -- state the unfolded slash of the coercion so `slash_mul` applies
  change (⇑f ∣[k] mapGL ℝ ((g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ)))) z =
    ((⇑f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ))) ∣[k] mapGL ℝ (g₁ : SL(2, ℤ))) z
  rw [map_mul, SlashAction.slash_mul]

/-- The diamond operator as a monoid homomorphism `(ZMod N)ˣ →* Module.End ℂ (...)`. -/
noncomputable def diamondOpHom [NeZero N] (k : ℤ) :
    (ZMod N)ˣ →* Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := diamondOp k
  map_one' := diamondOp_one k
  map_mul' := diamondOp_mul k

lemma diamondOpHom_apply [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) :
    diamondOpHom k d = diamondOp k d := (rfl)

noncomputable def diamondOpCuspAux (k : ℤ) (g : ↥(Gamma0 N)) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
      { toFun := ⇑f ∣[k] (mapGL ℝ (g : SL(2, ℤ)))
        slash_action_eq' _ hγ :=
          slash_mapGL_invariant_of_Gamma1_invariant g
            (fun _ hδ ↦ SlashInvariantFormClass.slash_action_eq f _ hδ) hγ }
      holo' := (CuspFormClass.holo f).slash k _
      zero_at_cusps' {c} hc _ hγ := by
        rw [← SlashAction.slash_mul, ← OnePoint.isZeroAt_infty_iff,
          ← OnePoint.IsZeroAt.smul_iff]
        exact CuspFormClass.zero_at_cusps f (isCusp_mul_mapGL_smul_infty g hc hγ) }
  map_add' f₁ f₂ := by
    ext z
    exact congr_fun (SlashAction.add_slash k (mapGL ℝ (g : SL(2, ℤ))) ⇑f₁ ⇑f₂) z
  map_smul' c f := by
    ext z
    -- the coercion of a bundled form slashes pointwise by definition; `change` states the
    -- unfolded form so that the slash-action lemma applies (no rewriting lemma exists here)
    change ((c • ⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z = c • _
    simp [ModularForm.smul_slash]

/-- Well-definedness for the cusp-form diamond operator. -/
theorem diamondOpCuspAux_eq_of_Gamma0Map_eq (k : ℤ) (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    diamondOpCuspAux k g₁ = diamondOpCuspAux k g₂ := by
  ext f z
  exact congr_fun (slash_eq_of_Gamma0Map_eq
    (fun _ hγ ↦ SlashInvariantFormClass.slash_action_eq f _ hγ) g₁ g₂ heq) z

/-- The cusp-form diamond operator indexed by `d : (ZMod N)ˣ`. -/
noncomputable def diamondOpCusp [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  diamondOpCuspAux k (Gamma0MapUnits_surjective d).choose

/-- `diamondOpCusp` equals `diamondOpCuspAux` on any representative. -/
theorem diamondOpCusp_eq (k : ℤ) (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : Gamma0MapUnits g = d) [NeZero N] :
    diamondOpCusp k d = diamondOpCuspAux k g :=
  diamondOpCuspAux_eq_of_Gamma0Map_eq k _ g
    (by simp [← Gamma0MapUnits_val, (Gamma0MapUnits_surjective d).choose_spec, hg])

@[simp]
theorem diamondOpCusp_one [NeZero N] (k : ℤ) : diamondOpCusp (N := N) k 1 = LinearMap.id := by
  rw [diamondOpCusp_eq k 1 1 (map_one _)]
  ext f z
  -- state the unfolded slash of the coercion so `slash_one` applies
  change (⇑f ∣[k] mapGL ℝ (1 : SL(2, ℤ))) z = f z
  simp only [map_one, SlashAction.slash_one]

theorem diamondOpCusp_mul [NeZero N] (k : ℤ) (d₁ d₂ : (ZMod N)ˣ) :
    diamondOpCusp k (d₁ * d₂) = (diamondOpCusp k d₁).comp (diamondOpCusp k d₂) := by
  obtain ⟨g₁, hg₁⟩ := Gamma0MapUnits_surjective (N := N) d₁
  obtain ⟨g₂, hg₂⟩ := Gamma0MapUnits_surjective (N := N) d₂
  rw [diamondOpCusp_eq k (d₁ * d₂) (g₂ * g₁) (by simp [map_mul, hg₁, hg₂, mul_comm]),
    diamondOpCusp_eq k d₁ g₁ hg₁, diamondOpCusp_eq k d₂ g₂ hg₂]
  ext f z
  -- state the unfolded slash of the coercion so `slash_mul` applies
  change (⇑f ∣[k] mapGL ℝ ((g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ)))) z =
    ((⇑f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ))) ∣[k] mapGL ℝ (g₁ : SL(2, ℤ))) z
  rw [map_mul, SlashAction.slash_mul]

/-- The cusp-form diamond operator as a monoid homomorphism. -/
noncomputable def diamondOpCuspHom [NeZero N] (k : ℤ) :
    (ZMod N)ˣ →* Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := diamondOpCusp k
  map_one' := diamondOpCusp_one k
  map_mul' := diamondOpCusp_mul k

lemma diamondOpCuspHom_apply [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) :
    diamondOpCuspHom k d = diamondOpCusp k d := (rfl)

/-- The nebentypus character space `S_k(Γ₁(N), χ)`: cusp forms on which every
diamond operator `⟨d⟩` acts by the scalar `χ(d)`. -/
noncomputable def cuspFormCharSpace [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, Module.End.eigenspace (diamondOpCuspHom k d) (↑(χ d))

/-- Membership in `S_k(Γ₁(N), χ)`: `f` is in the `χ`-eigenspace iff
`⟨d⟩ f = χ(d) • f` for every `d ∈ (ZMod N)ˣ`. -/
theorem mem_cuspFormCharSpace_iff [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ cuspFormCharSpace k χ ↔
    ∀ d : (ZMod N)ˣ, diamondOpCuspHom k d f = (↑(χ d) : ℂ) • f := by
  simp only [cuspFormCharSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- Diamond operators act by `χ(d)` on elements of `S_k(Γ₁(N), χ)`. -/
theorem diamondOpCusp_apply_charSpace [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (d : (ZMod N)ˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    diamondOpCuspHom k d f = (↑(χ d) : ℂ) • f :=
  (mem_cuspFormCharSpace_iff k χ f).mp hf d

/-- The modular-form nebentypus character space `M_k(Γ₁(N), χ)`. -/
noncomputable def modFormCharSpace [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, Module.End.eigenspace (diamondOpHom k d) (↑(χ d))

/-- Membership in `M_k(Γ₁(N), χ)`: `f` is in the `χ`-eigenspace iff `⟨d⟩ f = χ(d) • f`
for every `d ∈ (ZMod N)ˣ`. -/
theorem mem_modFormCharSpace_iff [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ modFormCharSpace k χ ↔
    ∀ d : (ZMod N)ˣ, diamondOpHom k d f = (↑(χ d) : ℂ) • f := by
  simp only [modFormCharSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- **Bridge**: for a `Gamma1`-invariant modular form `f`, membership in the
diamond-eigenspace `modFormCharSpace k χ₀` is equivalent to the classical nebentypus
relation `f ∣[k] g = χ₀(d_g) • f` for all `g ∈ Γ₀(N)`. -/
theorem modFormCharSpace_iff_nebentypus [NeZero N] (k : ℤ) (χ₀ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ modFormCharSpace k χ₀ ↔
    ∀ g : ↥(Gamma0 N),
      (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ₀ (Gamma0MapUnits g)) : ℂ) • ⇑f := by
  rw [mem_modFormCharSpace_iff]
  refine ⟨fun h g ↦ ?_, fun h d ↦ ?_⟩
  · have hd := h (Gamma0MapUnits g)
    rw [diamondOpHom_apply, diamondOp_eq_diamondOpAux k _ g rfl] at hd
    exact congr_arg (⇑· : ModularForm _ k → _) hd
  · obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
    rw [diamondOpHom_apply, diamondOp_eq_diamondOpAux k d g hg, ← hg]
    exact ModularForm.ext (congr_fun (h g))

/-- **Bridge (cusp forms)**: for a `Gamma1`-invariant cusp form `f`, membership in the
diamond-eigenspace `cuspFormCharSpace k χ₀` is equivalent to the classical nebentypus
relation `f ∣[k] g = χ₀(d_g) • f` for all `g ∈ Γ₀(N)`. -/
theorem cuspFormCharSpace_iff_nebentypus [NeZero N] (k : ℤ) (χ₀ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ cuspFormCharSpace k χ₀ ↔
    ∀ g : ↥(Gamma0 N),
      (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ₀ (Gamma0MapUnits g)) : ℂ) • ⇑f := by
  rw [mem_cuspFormCharSpace_iff]
  refine ⟨fun h g ↦ ?_, fun h d ↦ ?_⟩
  · have hd := h (Gamma0MapUnits g)
    rw [diamondOpCuspHom_apply, diamondOpCusp_eq k _ g rfl] at hd
    exact congr_arg (⇑· : CuspForm _ k → _) hd
  · obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
    rw [diamondOpCuspHom_apply, diamondOpCusp_eq k d g hg, ← hg]
    exact CuspForm.ext (congr_fun (h g))
