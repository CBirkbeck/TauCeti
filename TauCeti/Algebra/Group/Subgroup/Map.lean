/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Maps of subgroups

Mathlib's `MonoidHom.subgroupComap` sends the preimage `K.comap f` of a subgroup `K` to `K`.
Mathlib records that this map is surjective when `f` is
(`MonoidHom.subgroupComap_surjective_of_surjective`); this file records the companion fact for
injectivity. It also records how surjective homomorphisms act on centres and on derived subgroups.

An isomorphism carrying a subgroup `A` onto a subgroup `B` restricts to an isomorphism `↥A ≃* ↥B`,
and carries the coset space `G ⧸ A` bijectively onto `H ⧸ B`.
That restriction is `TauCeti.Subgroup.congrOfMapEq`, and every subgroup a construction transports
along an isomorphism — here the derived subgroup, elsewhere the fixed subgroup of an endomorphism —
uses it rather than repeating the composition of `MulEquiv.subgroupMap` with
`MulEquiv.subgroupCongr`.

## Main definitions

* `TauCeti.Subgroup.congrOfMapEq`: the isomorphism of subgroups restricted from an isomorphism of
  groups carrying the one onto the other.
* `TauCeti.commutatorCongr`: its instance for the derived subgroup.
* `MonoidHom.subgroupCongr`: a homomorphism of subgroups transported along equalities of its
  domain and codomain, for reading a construction through two presentations of the subgroups it
  connects.
* `TauCeti.QuotientGroup.congrOfMapEq`: its coset-space companion — an isomorphism carrying `A`
  onto `B` gives a bijection `G ⧸ A ≃ H ⧸ B`. Neither subgroup need be normal, which is what
  distinguishes it from Mathlib's `QuotientGroup.congr`.
* `TauCeti.QuotientGroup.congrOfSurjectiveOfKerLe`: the same for a *surjection* rather than an
  isomorphism, provided its kernel is already inside `A`. The kernel is then absorbed by the
  denominator and the index is unchanged, so a homomorphism that deliberately collapses part of
  the group — a projection onto a group that acts faithfully, say — still transports coset
  spaces.

## Main results

* `TauCeti.MonoidHom.subgroupComap_injective_of_injective`: `f.subgroupComap K` is injective when
  `f` is.
* `TauCeti.Subgroup.map_center_le`: a surjective homomorphism carries central elements to central
  elements.
* `MonoidHom.center_le_ker`: the centre lies in the kernel of a surjection onto a
  centreless group.
* `TauCeti.Subgroup.map_commutator_eq_commutator`: a surjective homomorphism carries the derived
  subgroup onto the derived subgroup.
* `Subgroup.map_conj_map`: the image of a conjugate subgroup is the conjugate of the image.
* `Subgroup.map_mk'_map_quotientGroupMap`: taking images in quotients commutes with the maps
  induced on quotients.
* `MonoidHom.subgroupCongr_injective`, `MonoidHom.subgroupCongr_surjective`: transport along
  equalities of the domain and codomain preserves injectivity and surjectivity.
-/

public section

namespace TauCeti

variable {G H : Type*} [Group G] [Group H]

/-- The comparison map from the preimage of a subgroup to that subgroup is injective as soon as the
underlying homomorphism is. Companion to Mathlib's
`MonoidHom.subgroupComap_surjective_of_surjective`. -/
theorem MonoidHom.subgroupComap_injective_of_injective {f : H →* G} (hf : Function.Injective f)
    (K : Subgroup G) : Function.Injective (f.subgroupComap K) :=
  fun _ _ hxy ↦ Subtype.ext (hf (congrArg Subtype.val hxy))

/-- A surjective homomorphism carries central elements to central elements. This is Mathlib's
`Subgroup.map_center_le_center` specialised to a bundled `G →* H`; `Subgroup.map_center_eq_center`
below strengthens `≤` to `=` for an isomorphism. -/
theorem Subgroup.map_center_le (f : G →* H) (hf : Function.Surjective f) :
    (Subgroup.center G).map f ≤ Subgroup.center H :=
  Subgroup.map_center_le_center hf

/-- An isomorphism of groups carries the centre onto the centre. -/
theorem Subgroup.map_center_eq_center (e : G ≃* H) :
    (Subgroup.center G).map (e : G →* H) = Subgroup.center H :=
  Subgroup.map_center_eq e

/-- The centre of a group lies in the kernel of every surjection onto a centreless group.

Mathlib's `Subgroup.map_center_le_center` bounds the image of the centre under any surjection by
`Subgroup.center H`; this lemma is the special case where that bound is `⊥`. -/
theorem _root_.MonoidHom.center_le_ker (f : G →* H) (hf : Function.Surjective f)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G ≤ f.ker :=
  (Subgroup.map_eq_bot_iff _).mp <| le_bot_iff.mp <| hH ▸ Subgroup.map_center_le_center hf

/-! ## Restricting an isomorphism to a subgroup -/

variable {K : Type*} [Group K]

/-- The isomorphism of subgroups restricted from an isomorphism of groups carrying the one onto the
other. It acts as `e` on elements, and its inverse as `e.symm`.

Use it rather than `MulEquiv.subgroupMap` whenever the target subgroup already has a name:
`subgroupMap` lands in the literal image `A.map e`, so every call site would otherwise compose it
with `MulEquiv.subgroupCongr` by hand. `QuotientGroup.congrOfMapEq` is the coset-space companion. -/
def Subgroup.congrOfMapEq (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) : ↥A ≃* ↥B :=
  (e.subgroupMap A).trans (MulEquiv.subgroupCongr h)

/-- The restriction `Subgroup.congrOfMapEq e h` agrees with `e` on underlying elements. Both
subgroups are implicit and pinned by `h`, so neither has to be named at a use site;
`Subgroup.coe_congrOfMapEq_symm_apply` is the companion statement for the inverse. -/
@[simp]
theorem Subgroup.coe_congrOfMapEq_apply (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) (x : ↥A) : (Subgroup.congrOfMapEq e h x : H) = e (x : G) := by
  -- `congrOfMapEq` is `(e.subgroupMap A).trans (MulEquiv.subgroupCongr h)`, and both halves act on
  -- the underlying element by `e` and by the identity; the invariant this proof rests on is that
  -- `MulEquiv.subgroupCongr` is a `Subtype`-transport, so it does not touch the carrier.
  rfl

/-- The inverse of the restriction `Subgroup.congrOfMapEq e h` agrees with `e.symm` on underlying
elements; the companion of `Subgroup.coe_congrOfMapEq_apply` for the inverse. It is the coerced
form, where Mathlib's `MulEquiv.subgroupMap_symm_apply` for the literal image `A.map e` returns
the subtype `⟨e.symm ↑y, _⟩`; `Subgroup.congrOfMapEq_symm` rewrites the whole inverse instead. -/
@[simp]
theorem Subgroup.coe_congrOfMapEq_symm_apply (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) (y : ↥B) :
    ((Subgroup.congrOfMapEq e h).symm y : G) = e.symm (y : H) := by
  -- the same invariant as `coe_congrOfMapEq_apply`, read through `.symm`: inverting a `trans` of a
  -- `subgroupMap` and a carrier-preserving `subgroupCongr` leaves `e.symm` acting on the carrier.
  rfl

/-- Restricting the identity isomorphism of `G` to a subgroup `A` it carries onto itself gives the
identity of `↥A`.

The map-equality hypothesis is explicit but pinned by unification with the left-hand side, so a use
site spells this `Subgroup.congrOfMapEq_refl _`. `Subgroup.congrOfMapEq_trans` and
`Subgroup.congrOfMapEq_symm` are the companion composition and inverse statements. -/
@[simp]
theorem Subgroup.congrOfMapEq_refl {A : Subgroup G} (h : A.map (MulEquiv.refl G : G →* G) = A) :
    Subgroup.congrOfMapEq (MulEquiv.refl G) h = MulEquiv.refl ↥A :=
  MulEquiv.ext fun x ↦ Subtype.ext <| by simp

/-- Restricting to subgroups is functorial: the restriction of `e.trans f` is the composite of the
restrictions of `e` and of `f`.

The composite's own map-equality hypothesis is derived from `h` and `h'`, so a use site supplies
only the two individual ones. `Subgroup.congrOfMapEq_refl` and `Subgroup.congrOfMapEq_symm` are the
companion identity and inverse statements. -/
@[simp]
theorem Subgroup.congrOfMapEq_trans (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) (f : H ≃* K) {C : Subgroup K} (h' : B.map (f : H →* K) = C) :
    (Subgroup.congrOfMapEq e h).trans (Subgroup.congrOfMapEq f h') = Subgroup.congrOfMapEq
      (e.trans f) (by rw [MulEquiv.coe_monoidHom_trans, ← _root_.Subgroup.map_map, h, h']) :=
  MulEquiv.ext fun x ↦ Subtype.ext <| by simp

-- Not `@[simp]`: with this in the simp set, `Subgroup.coe_congrOfMapEq_symm_apply` above is
-- provable by `simp`, which the `simpNF` linter rejects.
/-- Inverting the restriction of `e` to `A ≃* B` gives the restriction of `e.symm` to `B ≃* A`.

The equality `B.map e.symm = A` needed on the right is derived from `h`, so a use site supplies
only `h`. This is the whole-isomorphism form; `Subgroup.coe_congrOfMapEq_symm_apply` is the
pointwise one. -/
theorem Subgroup.congrOfMapEq_symm (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) : (Subgroup.congrOfMapEq e h).symm =
      Subgroup.congrOfMapEq e.symm ((_root_.Subgroup.map_symm_eq_iff_map_eq A).mpr h) :=
  MulEquiv.ext fun y ↦ Subtype.ext <| by simp

/-- The homomorphism of subgroups obtained from a homomorphism between two other subgroups by
transporting along equalities of the domain and of the codomain.

Mathlib's `MulEquiv.subgroupCongr` transports along a single equality of two subgroups of *one*
group; here the domain and the codomain live in different groups, so there is one equality at each
end. `MonoidHom.coe_subgroupCongr_apply` evaluates the result in the ambient group. -/
def _root_.MonoidHom.subgroupCongr {A A' : Subgroup G} {B B' : Subgroup H} (hA : A' = A)
    (hB : B' = B) (f : A →* B) : A' →* B' :=
  (MulEquiv.subgroupCongr hB).symm.toMonoidHom.comp (f.comp (MulEquiv.subgroupCongr hA).toMonoidHom)

/-- The transported homomorphism takes the same value in the ambient group as the original does
at the corresponding element. -/
@[simp]
theorem _root_.MonoidHom.coe_subgroupCongr_apply {A A' : Subgroup G} {B B' : Subgroup H}
    (hA : A' = A) (hB : B' = B) (f : A →* B) (x : A') :
    (f.subgroupCongr hA hB x : H) = f ⟨x, hA ▸ x.2⟩ := by
  simp only [MonoidHom.subgroupCongr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_symm_apply]
  exact congrArg (fun y => (f y : H)) (Subtype.ext (MulEquiv.subgroupCongr_apply hA x))

/-- Transporting the identity homomorphism along one equality of subgroups, on both sides, gives
the identity. -/
@[simp]
theorem _root_.MonoidHom.subgroupCongr_id {A A' : Subgroup G} (hA : A' = A) :
    (MonoidHom.id A).subgroupCongr hA hA = MonoidHom.id A' :=
  MonoidHom.ext fun x => (MulEquiv.subgroupCongr hA).symm_apply_apply x

/-- Transport commutes with composition: transporting `g.comp f` along the outer two equalities
agrees with transporting `f` and `g` separately through a common middle subgroup.

Not a `simp` lemma: the middle subgroup `B'` and its presentation `hB` occur only on the
right-hand side, so `simp` would have to invent them and would rewrite into an unrelated
instantiation. -/
theorem _root_.MonoidHom.subgroupCongr_comp {A A' : Subgroup G} {B B' : Subgroup H}
    {C C' : Subgroup K} (hA : A' = A) (hB : B' = B) (hC : C' = C) (f : A →* B) (g : B →* C) :
    (g.comp f).subgroupCongr hA hC = (g.subgroupCongr hB hC).comp (f.subgroupCongr hA hB) :=
  MonoidHom.ext fun x => by
    simp only [MonoidHom.subgroupCongr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]

/-- Transport along equalities of the domain and codomain preserves injectivity. -/
theorem _root_.MonoidHom.subgroupCongr_injective {A A' : Subgroup G} {B B' : Subgroup H}
    (hA : A' = A) (hB : B' = B) {f : A →* B} (hf : Function.Injective f) :
    Function.Injective (f.subgroupCongr hA hB) :=
  (MulEquiv.subgroupCongr hB).symm.injective.comp
    (hf.comp (MulEquiv.subgroupCongr hA).injective)

/-- Transport along equalities of the domain and codomain preserves surjectivity. -/
theorem _root_.MonoidHom.subgroupCongr_surjective {A A' : Subgroup G} {B B' : Subgroup H}
    (hA : A' = A) (hB : B' = B) {f : A →* B} (hf : Function.Surjective f) :
    Function.Surjective (f.subgroupCongr hA hB) :=
  (MulEquiv.subgroupCongr hB).symm.surjective.comp
    (hf.comp (MulEquiv.subgroupCongr hA).surjective)

/-! ## Transporting the derived subgroup -/

/-- A surjective homomorphism carries the derived subgroup onto the derived subgroup. -/
theorem Subgroup.map_commutator_eq_commutator {f : G →* H} (hf : Function.Surjective f) :
    (commutator G).map f = commutator H := by
  simpa using map_derivedSeries_eq hf 1

/-- The isomorphism of derived subgroups restricted from an isomorphism of groups. -/
def commutatorCongr (e : G ≃* H) : ↥(commutator G) ≃* ↥(commutator H) :=
  Subgroup.congrOfMapEq e (Subgroup.map_commutator_eq_commutator e.surjective)

@[simp]
theorem coe_commutatorCongr_apply (e : G ≃* H) (x : ↥(commutator G)) :
    (commutatorCongr e x : H) = e (x : G) :=
  Subgroup.coe_congrOfMapEq_apply e _ x

@[simp]
theorem coe_commutatorCongr_symm_apply (e : G ≃* H) (y : ↥(commutator H)) :
    ((commutatorCongr e).symm y : G) = e.symm (y : H) :=
  Subgroup.coe_congrOfMapEq_symm_apply e _ y

@[simp]
theorem commutatorCongr_refl :
    commutatorCongr (MulEquiv.refl G) = MulEquiv.refl ↥(commutator G) :=
  Subgroup.congrOfMapEq_refl _

@[simp]
theorem commutatorCongr_trans (e : G ≃* H) (f : H ≃* K) :
    (commutatorCongr e).trans (commutatorCongr f) = commutatorCongr (e.trans f) :=
  Subgroup.congrOfMapEq_trans e _ f _

-- Not `@[simp]`, for the reason given at `Subgroup.congrOfMapEq_symm`.
theorem commutatorCongr_symm (e : G ≃* H) :
    (commutatorCongr e).symm = commutatorCongr e.symm :=
  Subgroup.congrOfMapEq_symm e _

/-- The image of a conjugate subgroup `gRg⁻¹` under a homomorphism `f` is the conjugate of `f(R)`
by `f g`. -/
theorem _root_.Subgroup.map_conj_map (R : Subgroup G) (f : G →* H) (g : G) :
    (R.map (MulAut.conj g).toMonoidHom).map f = (R.map f).map (MulAut.conj (f g)).toMonoidHom := by
  have hf : f.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (f g)).toMonoidHom.comp f :=
    MonoidHom.ext fun x ↦ by simp
  rw [Subgroup.map_map, Subgroup.map_map, hf]

/-- The image of a subgroup in `G ⧸ N`, pushed forward along the map `G ⧸ N →* H ⧸ M` induced by
`f`, is the image in `H ⧸ M` of the image of the subgroup under `f`. -/
@[simp]
theorem _root_.Subgroup.map_mk'_map_quotientGroupMap (R : Subgroup G) {N : Subgroup G}
    {M : Subgroup H} [N.Normal] [M.Normal] (f : G →* H) (h : N ≤ M.comap f) :
    (R.map (QuotientGroup.mk' N)).map (QuotientGroup.map N M f h) =
      (R.map f).map (QuotientGroup.mk' M) := by
  have hf : (QuotientGroup.map N M f h).comp (QuotientGroup.mk' N) =
      (QuotientGroup.mk' M).comp f :=
    MonoidHom.ext fun x ↦ QuotientGroup.map_mk' N M f h x
  rw [Subgroup.map_map, Subgroup.map_map, hf]

/-! ## Transporting a coset space along an isomorphism -/

/-- **Coset spaces transport along an isomorphism.** If `e : G ≃* H` carries `A` onto `B`, then
`G ⧸ A ≃ H ⧸ B`, by `e` on representatives.

Neither subgroup is assumed normal, so this is an equivalence of coset *spaces*.
`QuotientGroup.congr` is the normal case, where the same data upgrades to a `MulEquiv`; it does
not apply to a subgroup like `Γ₁ ∩ gΓ₂g⁻¹`, which is where this is needed. It is the coset-space
companion of `Subgroup.congrOfMapEq` above. -/
def QuotientGroup.congrOfMapEq (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) : G ⧸ A ≃ H ⧸ B :=
  Quotient.congr e.toEquiv fun a b ↦ by
    subst h
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    simp [← map_inv, ← map_mul]

@[simp]
theorem QuotientGroup.congrOfMapEq_mk (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (h : A.map (e : G →* H) = B) (a : G) :
    QuotientGroup.congrOfMapEq e h (QuotientGroup.mk a) = QuotientGroup.mk (e a) := by
  unfold QuotientGroup.congrOfMapEq
  rfl

/-- **Coset spaces transport along a surjection whose kernel lies in the subgroup.** For `ψ`
surjective with `ker ψ ≤ A` and `A.map ψ = B`, the map `G ⧸ A → H ⧸ B` induced by `ψ` on
representatives is a bijection.

Injectivity of `ψ` is not needed: `ker ψ ≤ A` makes the denominator absorb the kernel, so the
index is unchanged. That is what lets a Hecke decomposition be carried into a group acting
faithfully on the upper half-plane, where the collapsing of `±1` is the point rather than a
defect. As with `QuotientGroup.congrOfMapEq`, neither subgroup need be normal. -/
noncomputable def QuotientGroup.congrOfSurjectiveOfKerLe (ψ : G →* H)
    (hsurj : Function.Surjective ψ) {A : Subgroup G} {B : Subgroup H}
    (hker : ψ.ker ≤ A) (hmap : A.map ψ = B) : G ⧸ A ≃ H ⧸ B := by
  classical
  -- `ker ψ ≤ A` is exactly what makes `A` the full preimage of `B`, and membership in a preimage
  -- is the whole content of the coset relation matching on both sides
  have hcomap : B.comap ψ = A := hmap ▸ Subgroup.comap_map_eq_self hker
  have key : ∀ a b : G, (a⁻¹ * b ∈ A) ↔ ((ψ a)⁻¹ * ψ b ∈ B) := fun a b ↦ by
    rw [← hcomap, Subgroup.mem_comap, map_mul, map_inv]
  refine Equiv.ofBijective (Quotient.map' ψ ?_) ⟨?_, ?_⟩
  · intro a b hab
    exact QuotientGroup.leftRel_apply.mpr
      ((key a b).mp (QuotientGroup.leftRel_apply.mp hab))
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | _ a =>
    induction y using QuotientGroup.induction_on with | _ b =>
    exact QuotientGroup.eq.mpr ((key a b).mpr (QuotientGroup.eq.mp hxy))
  · exact Quotient.map_surjective _ hsurj

@[simp]
theorem QuotientGroup.congrOfSurjectiveOfKerLe_mk (ψ : G →* H)
    (hsurj : Function.Surjective ψ) {A : Subgroup G} {B : Subgroup H}
    (hker : ψ.ker ≤ A) (hmap : A.map ψ = B) (a : G) :
    QuotientGroup.congrOfSurjectiveOfKerLe ψ hsurj hker hmap (QuotientGroup.mk a) =
      QuotientGroup.mk (ψ a) := by
  -- This lemma IS the abstraction barrier: `congrOfSurjectiveOfKerLe` is an `Equiv.ofBijective`
  -- around `Quotient.map' ψ`, whose `toFun` is that map, so on a class `⟦a⟧` it reduces to
  -- `⟦ψ a⟧` — the content of Mathlib's `Quotient.map'_mk''`, which cannot be cited directly here
  -- because `Equiv.ofBijective` has no `_apply` lemma in Mathlib to strip the wrapper first
  -- (checked: only `Equiv.ofBijective_apply_symm_apply` exists). Downstream code rewrites with
  -- this lemma and never sees either wrapper, which is what keeps the implementation free to move.
  unfold QuotientGroup.congrOfSurjectiveOfKerLe
  rfl

end TauCeti
