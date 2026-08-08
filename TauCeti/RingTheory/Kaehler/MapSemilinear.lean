/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Semilinear functoriality of Kähler differentials along algebra homomorphisms

For an `R`-algebra homomorphism `f : A →ₐ[R] B`, the induced map on Kähler differentials sends
`D x` to `D (f x)`. It is not linear but `f`-**semilinear** —
`mapSemilinear f (a • ω) = f a • mapSemilinear f ω` — so it is packaged as a semilinear map
`Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R]`, following the precedent of `LinearMap.frobenius`. The
motivating special case is an algebra *endomorphism* `f : S →ₐ[R] S` (for instance Frobenius),
where this is the pullback of differentials along `f`.

Mathlib's `KaehlerDifferential.map` is functoriality for a *tower* `[Algebra A B]`
`[IsScalarTower R A B]`, so it cannot state this map: for an arbitrary `f : A →ₐ[R] B` no
`Algebra A B` instance exists, and for an endomorphism, installing one would clash with
`Algebra.id`. The two structures induced by `f` do exist *locally*, however, and `mapSemilinear` is
`KaehlerDifferential.map` under those local `letI` instances, repackaged with the `A`-action on
the target unfolded into `f`-semilinearity — which is exactly the statement that survives
outside the `letI` scope.

## Main definitions

* `KaehlerDifferential.mapSemilinear f : Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R]`

## Main results

* `KaehlerDifferential.mapSemilinear_D`: `mapSemilinear f (D x) = D (f x)`.
* `KaehlerDifferential.mapSemilinear_smul`: the semilinearity law, with `f` applied rather than
  `f.toRingHom`.
* `KaehlerDifferential.mapSemilinear_ext`: semilinear maps agreeing on the range of `D` are
  equal.
* `KaehlerDifferential.mapSemilinear_id_apply`, `mapSemilinear_id`: the identity acts as the
  identity.
* `KaehlerDifferential.mapSemilinear_comp_apply`, `mapSemilinear_comp`: compatibility with
  composition.

Proofs about `mapSemilinear` use receiver-explicit lemmas (`map_add`, `map_smulₛₗ`, …) rather
than unrestricted `simp`: `simp` first normalises the semilinearity index
`(AlgHom.id R A).toRingHom` to `RingHom.id A` inside the *type* of the map, retyping the
application so that no lemma matches afterwards.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Auxiliary/PullbackKaehler.lean`, declarations `AlgHom.pullbackKaehler`,
`pullbackKaehler_D`, `pullbackKaehler_smul_R`, `pullbackKaehler_smul_S`, `pullbackKaehler_comp`
and `pullbackKaehler_id`. The source treats an endomorphism of a fixed `S`, exports an
`AddMonoidHom` with hand-stated semilinearity lemmas, and builds the map from scratch through a
public `TwistedKaehler` module; here the map is generalised to an arbitrary `R`-algebra
homomorphism `A →ₐ[R] B`, constructed from Mathlib's `KaehlerDifferential.map`, and exported as
the semilinear map, whose type already carries the scalar law the source stated by hand.
-/

namespace KaehlerDifferential

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

-- The scalar bridge between the semilinearity index `f.toRingHom` and `f` itself, in applied
-- form: the unapplied `AlgHom.toRingHom_eq_coe` cannot be used by `rw` here, since `f.toRingHom`
-- also occurs in the *type* of `mapSemilinear f` and abstracting it breaks the motive.
theorem toRingHom_apply (f : A →ₐ[R] B) (a : A) : f.toRingHom a = f a := rfl

-- Every differential is in the span of the range of `D`, so pointwise identities may be proved
-- by span induction; the scalar step is `mapSemilinear_smul`.
theorem mem_span_range (ω : Ω[A⁄R]) : ω ∈ Submodule.span A (Set.range (D R A)) := by
  rw [span_range_derivation]; trivial

public section

/-- **The map of Kähler differentials along an `R`-algebra homomorphism** `f : A →ₐ[R] B`,
characterised by `mapSemilinear f (D x) = D (f x)`. It is `f`-semilinear:
`mapSemilinear f (a • ω) = f a • mapSemilinear f ω` (`mapSemilinear_smul`).

This is `KaehlerDifferential.map` under the local `Algebra A B` structure induced by `f`,
repackaged semilinearly so that the statement survives outside that instance's scope. -/
noncomputable def mapSemilinear (f : A →ₐ[R] B) : Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R] :=
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  { toFun := KaehlerDifferential.map R R A B
    map_add' := map_add _
    map_smul' := fun a ω => by
      -- The `A`-action induced by `f` on the target unfolds to acting through `f`.
      rw [LinearMap.map_smul]
      exact (IsScalarTower.algebraMap_smul B a (KaehlerDifferential.map R R A B ω)).symm }

/-- `mapSemilinear f` sends `D x` to `D (f x)`. -/
@[simp]
theorem mapSemilinear_D (f : A →ₐ[R] B) (x : A) : mapSemilinear f (D R A x) = D R B (f x) :=
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  KaehlerDifferential.map_D R R A B x

/-- The semilinearity law of `mapSemilinear`, stated with `f` applied rather than
`f.toRingHom`. -/
@[simp]
theorem mapSemilinear_smul (f : A →ₐ[R] B) (a : A) (ω : Ω[A⁄R]) :
    mapSemilinear f (a • ω) = f a • mapSemilinear f ω := by
  rw [map_smulₛₗ, toRingHom_apply]

/-- Semilinear maps out of `Ω[A⁄R]` are determined by their values on the range of `D`
(which spans, `span_range_derivation`); this is the sense in which `mapSemilinear_D`
characterises `mapSemilinear`. -/
theorem mapSemilinear_ext {f : A →ₐ[R] B} {φ ψ : Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R]}
    (h : ∀ x, φ (D R A x) = ψ (D R A x)) : φ = ψ :=
  LinearMap.ext_on (span_range_derivation R A) (by rintro _ ⟨x, rfl⟩; exact h x)

/-- The map along the identity fixes every differential. -/
@[simp]
theorem mapSemilinear_id_apply (ω : Ω[A⁄R]) : mapSemilinear (AlgHom.id R A) ω = ω := by
  induction mem_span_range ω using Submodule.span_induction with
  | mem ω hω => obtain ⟨x, rfl⟩ := hω; rw [mapSemilinear_D, AlgHom.id_apply]
  | zero => exact map_zero _
  | add ω₁ ω₂ _ _ ih₁ ih₂ => rw [map_add, ih₁, ih₂]
  | smul a ω _ ih => rw [mapSemilinear_smul, ih, AlgHom.id_apply]

/-- `mapSemilinear` is functorial: mapping along `f.comp g` is mapping along `g`, then along
`f`. -/
@[simp]
theorem mapSemilinear_comp_apply (f : B →ₐ[R] C) (g : A →ₐ[R] B) (ω : Ω[A⁄R]) :
    mapSemilinear (f.comp g) ω = mapSemilinear f (mapSemilinear g ω) := by
  induction mem_span_range ω using Submodule.span_induction with
  | mem ω hω => obtain ⟨x, rfl⟩ := hω; rw [mapSemilinear_D, mapSemilinear_D, mapSemilinear_D,
      AlgHom.comp_apply]
  | zero => rw [map_zero, map_zero, map_zero]
  | add ω₁ ω₂ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, ih₁, ih₂]
  | smul a ω _ ih => rw [mapSemilinear_smul, mapSemilinear_smul, mapSemilinear_smul, ih,
      AlgHom.comp_apply]

/-- The map along the identity is the identity, as (plainly linear) maps. -/
theorem mapSemilinear_id :
    (mapSemilinear (AlgHom.id R A) : Ω[A⁄R] →ₗ[A] Ω[A⁄R]) = LinearMap.id :=
  LinearMap.ext mapSemilinear_id_apply

/-- Functoriality of `mapSemilinear` at map level; the composite's scalar law is supplied by
Mathlib's `RingHomCompTriple` instance for composed algebra maps. -/
theorem mapSemilinear_comp (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    mapSemilinear (f.comp g) = (mapSemilinear f).comp (mapSemilinear g) :=
  LinearMap.ext (mapSemilinear_comp_apply f g)

end

end KaehlerDifferential
