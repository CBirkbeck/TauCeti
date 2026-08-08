/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Group.TransferInstance

/-!
# Semilinear functoriality of Kähler differentials along algebra homomorphisms

For an `R`-algebra homomorphism `f : A →ₐ[R] B`, the induced map on Kähler differentials sends
`D x` to `D (f x)`. It is not linear but `f`-**semilinear** —
`mapAlgHom f (a • ω) = f a • mapAlgHom f ω` — so it is packaged as a semilinear map
`Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R]`, following the precedent of `LinearMap.frobenius`. The
motivating special case is an algebra *endomorphism* `f : S →ₐ[R] S` (for instance Frobenius),
where this is the pullback of differentials along `f`.

Mathlib's existing functoriality does not give this map:

* `KaehlerDifferential.map R S A B` requires `[Algebra A B]` with `[IsScalarTower R A B]` — a
  *tower*, not a homomorphism. For an arbitrary `f : A →ₐ[R] B` no such instance exists (and for
  an endomorphism, instantiating it would install a second `Algebra S S` instance clashing with
  `Algebra.id`).
* The category-level `CommRingCat.KaehlerDifferential.map` builds its modules through
  `RingHom.toAlgebra` of the given morphisms, so its object
  `CommRingCat.KaehlerDifferential (ofHom (algebraMap R S))` is `Ω` for the instance
  `(algebraMap R S).toAlgebra`, which is not definitionally the ambient `Algebra R S`; its
  carrier does not typecheck as `Ω[S⁄R]` (compiler-checked), and Mathlib has no bridge between
  the two.

Instead the map comes from the universal property: `x ↦ D (f x)` is a derivation into a copy of
`Ω[B⁄R]` whose `A`-action is twisted through `f`, and `Derivation.liftKaehlerDifferential`
linearises it. The twisted copy is a module-private one-field structure — a type synonym will
not do, because a synonym is definitionally equal to `Ω[B⁄R]` and instance resolution then
cannot keep the twisted and untwisted actions apart.

## Main definitions

* `KaehlerDifferential.mapAlgHom f : Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R]`

## Main results

* `KaehlerDifferential.mapAlgHom_D`: `mapAlgHom f (D x) = D (f x)`.
* `KaehlerDifferential.mapAlgHom_smul`: the semilinearity law, with `f` applied rather than
  `f.toRingHom`.
* `KaehlerDifferential.mapAlgHom_id_apply`, `mapAlgHom_id`: the identity acts as the identity.
* `KaehlerDifferential.mapAlgHom_comp_apply`, `mapAlgHom_comp`: compatibility with composition.

Proofs about `mapAlgHom` use receiver-explicit lemmas (`(mapAlgHom f).map_add`, `map_smulₛₗ`, …)
rather than unrestricted `simp`: `simp` first normalises the semilinearity index
`(AlgHom.id R A).toRingHom` to `RingHom.id A` inside the *type* of the map, retyping the
application so that no lemma matches afterwards.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Auxiliary/PullbackKaehler.lean`, declarations `AlgHom.pullbackKaehler`,
`pullbackKaehler_D`, `pullbackKaehler_smul_R`, `pullbackKaehler_smul_S`, `pullbackKaehler_comp`
and `pullbackKaehler_id`. The source treats an endomorphism of a fixed `S` and exports an
`AddMonoidHom` together with separate semilinearity lemmas and a public `TwistedKaehler` module;
here the map is generalised to an arbitrary `R`-algebra homomorphism `A →ₐ[R] B`, the twisted
carrier is module-private implementation detail, and the export is the semilinear map, whose
type already carries the scalar law the source stated by hand.
-/

namespace KaehlerDifferential

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/- Implementation for `mapAlgHom`. Everything here except the bare structure `Twisted` is
module-private; the structure itself must be public because the `structureInType` environment
linter cannot process a name-mangled projection (this holds for both `private` and
module-private declarations, and the linter allowlist is not writable from this repository's
AI-owned surface). -/

public section

/-- Implementation carrier for `KaehlerDifferential.mapAlgHom` — **not intended for use**: a
copy of `Ω[B⁄R]` whose `A`-action is twisted through `f`, so that `x ↦ D (f x)` becomes an
honest `A`-derivation into it. Every instance and lemma about it is module-private, so nothing
can be built on it from outside this file; only the structure itself is public, because the
environment linter cannot process a name-mangled projection. A structure rather than a type
synonym: a synonym is definitionally equal to `Ω[B⁄R]`, and instance resolution then conflates
the twisted and untwisted actions. -/
structure Twisted (f : A →ₐ[R] B) : Type _ where
  /-- The underlying differential. -/
  out : Ω[B⁄R]

end

namespace Twisted

variable (f : A →ₐ[R] B)

def equiv : Twisted f ≃ Ω[B⁄R] where
  toFun := out
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup (Twisted f) := (equiv f).addCommGroup

theorem out_injective : Function.Injective (out (f := f)) :=
  fun a b h => by cases a; cases b; cases h; rfl

theorem out_add (m n : Twisted f) : (m + n).out = m.out + n.out := rfl

theorem out_zero : (0 : Twisted f).out = 0 := rfl

-- The twisted `A`-action: `a` acts as `f a` does on the underlying differential.
noncomputable instance : SMul A (Twisted f) := ⟨fun a m => ⟨f a • m.out⟩⟩

theorem out_smul (a : A) (m : Twisted f) : (a • m).out = f a • m.out := rfl

noncomputable instance : Module A (Twisted f) where
  one_smul m := out_injective f <| by rw [out_smul, map_one, one_smul]
  mul_smul a b m := out_injective f <| by
    rw [out_smul, out_smul, out_smul, map_mul, mul_smul]
  smul_zero a := out_injective f <| by rw [out_smul, out_zero, smul_zero]
  smul_add a m n := out_injective f <| by
    rw [out_smul, out_add, out_add, out_smul, out_smul, smul_add]
  add_smul a b m := out_injective f <| by
    rw [out_smul, out_add, out_smul, out_smul, map_add, add_smul]
  zero_smul m := out_injective f <| by rw [out_smul, out_zero, map_zero, zero_smul]

-- The untwisted `R`-action: `f` fixes `R`, so twisting through `f` changes nothing over `R`.
noncomputable instance : SMul R (Twisted f) := ⟨fun r m => ⟨r • m.out⟩⟩

theorem out_smul_r (r : R) (m : Twisted f) : (r • m).out = r • m.out := rfl

noncomputable instance : Module R (Twisted f) where
  one_smul m := out_injective f <| by rw [out_smul_r, one_smul]
  mul_smul a b m := out_injective f <| by rw [out_smul_r, out_smul_r, out_smul_r, mul_smul]
  smul_zero r := out_injective f <| by rw [out_smul_r, out_zero, smul_zero]
  smul_add r m n := out_injective f <| by
    rw [out_smul_r, out_add, out_add, out_smul_r, out_smul_r, smul_add]
  add_smul a b m := out_injective f <| by
    rw [out_smul_r, out_add, out_smul_r, out_smul_r, add_smul]
  zero_smul m := out_injective f <| by rw [out_smul_r, out_zero, zero_smul]

instance : IsScalarTower R A (Twisted f) where
  smul_assoc r a m := out_injective f <| by
    -- The `A`-action applies `f`, which fixes `R` (`f.commutes`); the `R`-action is untwisted.
    rw [out_smul, out_smul_r, out_smul, Algebra.smul_def, map_mul, f.commutes,
      ← Algebra.smul_def, smul_assoc]

end Twisted

-- `x ↦ D (f x)`, as a derivation into the twisted carrier: the Leibniz rule
-- `D (f (a b)) = f a • D (f b) + f b • D (f a)` is exactly the twisted `A`-linearity.
noncomputable def twistedD (f : A →ₐ[R] B) : Derivation R A (Twisted f) where
  toFun x := ⟨D R B (f x)⟩
  map_add' x y := Twisted.out_injective f <| by rw [Twisted.out_add]; simp
  map_smul' r x := Twisted.out_injective f <| by rw [RingHom.id_apply, Twisted.out_smul_r]; simp
  map_one_eq_zero' := Twisted.out_injective f <| by rw [Twisted.out_zero]; simp
  leibniz' a b := Twisted.out_injective f <| by
    rw [Twisted.out_add, Twisted.out_smul, Twisted.out_smul]
    simp [Derivation.leibniz]

-- The scalar bridge between the semilinearity index `f.toRingHom` and `f` itself, in applied
-- form: the unapplied `AlgHom.toRingHom_eq_coe` cannot be used by `rw` here, since `f.toRingHom`
-- also occurs in the *type* of `mapAlgHom f` and abstracting it breaks the motive.
theorem toRingHom_apply (f : A →ₐ[R] B) (a : A) : f.toRingHom a = f a := rfl

-- Every differential is in the span of the range of `D`, so pointwise identities may be proved
-- by span induction; the scalar step is `mapAlgHom_smul`.
theorem mem_span_range (ω : Ω[A⁄R]) : ω ∈ Submodule.span A (Set.range (D R A)) := by
  rw [span_range_derivation]; trivial

public section

/-- **The map of Kähler differentials along an `R`-algebra homomorphism** `f : A →ₐ[R] B`,
characterised by `mapAlgHom f (D x) = D (f x)`. It is `f`-semilinear:
`mapAlgHom f (a • ω) = f a • mapAlgHom f ω` (`mapAlgHom_smul`). -/
noncomputable def mapAlgHom (f : A →ₐ[R] B) : Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R] where
  toFun ω := ((twistedD f).liftKaehlerDifferential ω).out
  map_add' ω₁ ω₂ := by rw [map_add, Twisted.out_add]
  map_smul' a ω := by
    -- `A`-linearity of the lift into the twisted carrier is `f`-semilinearity downstairs.
    rw [LinearMap.map_smul, Twisted.out_smul, toRingHom_apply]

/-- `mapAlgHom f` sends `D x` to `D (f x)`. -/
@[simp]
theorem mapAlgHom_D (f : A →ₐ[R] B) (x : A) : mapAlgHom f (D R A x) = D R B (f x) :=
  congrArg Twisted.out ((twistedD f).liftKaehlerDifferential_comp_D x)

/-- The semilinearity law of `mapAlgHom`, stated with `f` applied rather than `f.toRingHom`. -/
@[simp]
theorem mapAlgHom_smul (f : A →ₐ[R] B) (a : A) (ω : Ω[A⁄R]) :
    mapAlgHom f (a • ω) = f a • mapAlgHom f ω := by
  rw [map_smulₛₗ, toRingHom_apply]

/-- The map along the identity fixes every differential. -/
@[simp]
theorem mapAlgHom_id_apply (ω : Ω[A⁄R]) : mapAlgHom (AlgHom.id R A) ω = ω := by
  induction mem_span_range ω using Submodule.span_induction with
  | mem ω hω => obtain ⟨x, rfl⟩ := hω; rw [mapAlgHom_D, AlgHom.id_apply]
  | zero => exact map_zero _
  | add ω₁ ω₂ _ _ ih₁ ih₂ => rw [map_add, ih₁, ih₂]
  | smul a ω _ ih => rw [mapAlgHom_smul, ih, AlgHom.id_apply]

/-- `mapAlgHom` is functorial: mapping along `f.comp g` is mapping along `g`, then along `f`. -/
theorem mapAlgHom_comp_apply (f : B →ₐ[R] C) (g : A →ₐ[R] B) (ω : Ω[A⁄R]) :
    mapAlgHom (f.comp g) ω = mapAlgHom f (mapAlgHom g ω) := by
  induction mem_span_range ω using Submodule.span_induction with
  | mem ω hω => obtain ⟨x, rfl⟩ := hω; rw [mapAlgHom_D, mapAlgHom_D, mapAlgHom_D,
      AlgHom.comp_apply]
  | zero => rw [map_zero, map_zero, map_zero]
  | add ω₁ ω₂ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, ih₁, ih₂]
  | smul a ω _ ih => rw [mapAlgHom_smul, mapAlgHom_smul, mapAlgHom_smul, ih, AlgHom.comp_apply]

/-- The map along the identity is the identity, as (plainly linear) maps. -/
theorem mapAlgHom_id :
    (mapAlgHom (AlgHom.id R A) : Ω[A⁄R] →ₗ[A] Ω[A⁄R]) = LinearMap.id :=
  LinearMap.ext mapAlgHom_id_apply

/-- Functoriality of `mapAlgHom` at map level; the composite's scalar law is supplied by
Mathlib's `RingHomCompTriple` instance for composed algebra maps. -/
theorem mapAlgHom_comp (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    mapAlgHom (f.comp g) = (mapAlgHom f).comp (mapAlgHom g) :=
  LinearMap.ext (mapAlgHom_comp_apply f g)

end

end KaehlerDifferential
