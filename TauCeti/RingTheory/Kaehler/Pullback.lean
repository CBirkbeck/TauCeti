/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Group.TransferInstance

/-!
# Pullback of Kähler differentials along an algebra endomorphism

For an `R`-algebra endomorphism `f : S →ₐ[R] S`, the pullback on Kähler differentials is the map
`Ω[S⁄R] → Ω[S⁄R]` sending `D x` to `D (f x)`. It is not `S`-linear but `f`-**semilinear** —
`pullback f (s • ω) = f s • pullback f ω` — so it is packaged as a semilinear map
`Ω[S⁄R] →ₛₗ[f.toRingHom] Ω[S⁄R]`, following the precedent of `LinearMap.frobenius`.

Mathlib's `KaehlerDifferential.map` does not specialise to this: instantiating its target algebra
at `S` with the structure given by `f` would install a second `Algebra S S` instance clashing with
`Algebra.id`. Instead the map comes from the universal property: `x ↦ D (f x)` is a derivation
into a copy of `Ω[S⁄R]` whose `S`-action is twisted through `f`, and
`Derivation.liftKaehlerDifferential` linearises it. The twisted copy is a private one-field
structure — a type synonym will not do, because a synonym is definitionally equal to `Ω[S⁄R]` and
instance resolution then cannot keep the twisted and untwisted `S`-actions apart.

## Main definitions

* `KaehlerDifferential.pullback f : Ω[S⁄R] →ₛₗ[f.toRingHom] Ω[S⁄R]`

## Main results

* `KaehlerDifferential.pullback_D`: `pullback f (D x) = D (f x)`.
* `KaehlerDifferential.pullback_id_apply`: `pullback (AlgHom.id R S) ω = ω`.
* `KaehlerDifferential.pullback_comp_apply`: `pullback (f.comp g) ω = pullback f (pullback g ω)`.

* `KaehlerDifferential.pullback_id`, `pullback_comp`: the same at map level.

Proofs about `pullback` use receiver-explicit lemmas (`(pullback f).map_add`, `map_smulₛₗ`, …)
rather than unrestricted `simp`: `simp` first normalises the semilinearity index
`(AlgHom.id R S).toRingHom` to `RingHom.id S` inside the *type* of the map, retyping the
application so that no lemma matches afterwards.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Auxiliary/PullbackKaehler.lean`, declarations `AlgHom.pullbackKaehler`,
`pullbackKaehler_D`, `pullbackKaehler_smul_R`, `pullbackKaehler_smul_S`, `pullbackKaehler_comp`
and `pullbackKaehler_id`. The source exports an `AddMonoidHom` together with separate
semilinearity lemmas and a public `TwistedKaehler` module; here the twisted carrier is private
implementation detail and the export is the semilinear map, whose type already carries the scalar
law the source stated by hand.
-/

public section

namespace KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Implementation carrier for `KaehlerDifferential.pullback` — **not intended for use**: a copy
of `Ω[S⁄R]` whose `S`-action is twisted through `f`, so that `x ↦ D (f x)` becomes an honest
`S`-derivation into it. Every instance and lemma about it is private, so nothing can be built on
it from outside this file; only the structure itself is public, because the environment linter
cannot process a private projection. A structure rather than a type synonym: a synonym is
definitionally equal to `Ω[S⁄R]`, and instance resolution then conflates the twisted and
untwisted actions. -/
structure Twisted (f : S →ₐ[R] S) : Type _ where
  /-- The underlying differential. -/
  out : Ω[S⁄R]

private def twistedEquiv (f : S →ₐ[R] S) : Twisted f ≃ Ω[S⁄R] where
  toFun := Twisted.out
  invFun := Twisted.mk
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable instance (f : S →ₐ[R] S) : AddCommGroup (Twisted f) :=
  (twistedEquiv f).addCommGroup

private theorem out_injective (f : S →ₐ[R] S) : Function.Injective (Twisted.out (f := f)) :=
  fun a b h => by cases a; cases b; cases h; rfl

private theorem out_add (f : S →ₐ[R] S) (m n : Twisted f) :
    (m + n).out = m.out + n.out := rfl

private theorem out_zero (f : S →ₐ[R] S) : (0 : Twisted f).out = 0 := rfl

-- The twisted `S`-action: `s` acts as `f s` does on the underlying differential.
private noncomputable instance (f : S →ₐ[R] S) : SMul S (Twisted f) :=
  ⟨fun s m => ⟨f s • m.out⟩⟩

private theorem out_smul (f : S →ₐ[R] S) (s : S) (m : Twisted f) :
    (s • m).out = f s • m.out := rfl

private noncomputable instance (f : S →ₐ[R] S) : Module S (Twisted f) where
  one_smul m := out_injective f <| by rw [out_smul, map_one, one_smul]
  mul_smul a b m := out_injective f <| by
    rw [out_smul, out_smul, out_smul, map_mul, mul_smul]
  smul_zero s := out_injective f <| by rw [out_smul, out_zero, smul_zero]
  smul_add s m n := out_injective f <| by
    rw [out_smul, out_add, out_add, out_smul, out_smul, smul_add]
  add_smul a b m := out_injective f <| by
    rw [out_smul, out_add, out_smul, out_smul, map_add, add_smul]
  zero_smul m := out_injective f <| by rw [out_smul, out_zero, map_zero, zero_smul]

-- The untwisted `R`-action: `f` fixes `R`, so twisting through `f` changes nothing over `R`.
private noncomputable instance (f : S →ₐ[R] S) : SMul R (Twisted f) :=
  ⟨fun r m => ⟨r • m.out⟩⟩

private theorem out_smul_r (f : S →ₐ[R] S) (r : R) (m : Twisted f) :
    (r • m).out = r • m.out := rfl

private noncomputable instance (f : S →ₐ[R] S) : Module R (Twisted f) where
  one_smul m := out_injective f <| by rw [out_smul_r, one_smul]
  mul_smul a b m := out_injective f <| by rw [out_smul_r, out_smul_r, out_smul_r, mul_smul]
  smul_zero r := out_injective f <| by rw [out_smul_r, out_zero, smul_zero]
  smul_add r m n := out_injective f <| by
    rw [out_smul_r, out_add, out_add, out_smul_r, out_smul_r, smul_add]
  add_smul a b m := out_injective f <| by
    rw [out_smul_r, out_add, out_smul_r, out_smul_r, add_smul]
  zero_smul m := out_injective f <| by rw [out_smul_r, out_zero, zero_smul]

private instance (f : S →ₐ[R] S) : IsScalarTower R S (Twisted f) where
  smul_assoc r s m := out_injective f <| by
    -- The `S`-action applies `f`, which fixes `R` (`f.commutes`); the `R`-action is untwisted.
    rw [out_smul, out_smul_r, out_smul, Algebra.smul_def, map_mul, f.commutes,
      ← Algebra.smul_def, smul_assoc]

-- `x ↦ D (f x)`, as a derivation into the twisted carrier: the Leibniz rule
-- `D (f (a b)) = f a • D (f b) + f b • D (f a)` is exactly the twisted `S`-linearity.
private noncomputable def twistedD (f : S →ₐ[R] S) : Derivation R S (Twisted f) where
  toFun x := ⟨D R S (f x)⟩
  map_add' x y := out_injective f <| by rw [out_add]; simp
  map_smul' r x := out_injective f <| by rw [RingHom.id_apply, out_smul_r]; simp
  map_one_eq_zero' := out_injective f <| by rw [out_zero]; simp
  leibniz' a b := out_injective f <| by
    rw [out_add, out_smul, out_smul]
    simp [Derivation.leibniz]

/-- **Pullback of Kähler differentials along an algebra endomorphism**, characterised by
`pullback f (D x) = D (f x)`. It is `f`-semilinear: `pullback f (s • ω) = f s • pullback f ω`. -/
noncomputable def pullback (f : S →ₐ[R] S) : Ω[S⁄R] →ₛₗ[f.toRingHom] Ω[S⁄R] where
  toFun ω := ((twistedD f).liftKaehlerDifferential ω).out
  map_add' ω₁ ω₂ := by rw [map_add, out_add]
  map_smul' s ω := by
    -- `S`-linearity of the lift into the twisted carrier is `f`-semilinearity downstairs.
    rw [LinearMap.map_smul, out_smul]; rfl

/-- The characterising property of the pullback: `pullback f` sends `D x` to `D (f x)`. -/
@[simp]
theorem pullback_D (f : S →ₐ[R] S) (x : S) : pullback f (D R S x) = D R S (f x) :=
  congrArg Twisted.out ((twistedD f).liftKaehlerDifferential_comp_D x)

-- Every differential is in the span of the range of `D`, so pointwise identities may be proved
-- by span induction; the scalar step uses the semilinearity `map_smulₛₗ`.
private theorem mem_span_range (ω : Ω[S⁄R]) : ω ∈ Submodule.span S (Set.range (D R S)) := by
  rw [span_range_derivation]; trivial

/-- The pullback along the identity fixes every differential. -/
@[simp]
theorem pullback_id_apply (ω : Ω[S⁄R]) : pullback (AlgHom.id R S) ω = ω := by
  induction mem_span_range ω using Submodule.span_induction with
  | mem ω hω => obtain ⟨x, rfl⟩ := hω; rw [pullback_D, AlgHom.id_apply]
  | zero => exact map_zero _
  | add ω₁ ω₂ _ _ ih₁ ih₂ => rw [map_add, ih₁, ih₂]
  | smul s ω _ ih =>
    -- `map_smulₛₗ` produces `(AlgHom.id R S).toRingHom s • ω`, which is `s • ω` definitionally.
    rw [map_smulₛₗ, ih]; rfl

/-- Pullback preserves composition: pulling back along `f.comp g` is pulling back along `g`,
then along `f`. -/
theorem pullback_comp_apply (f g : S →ₐ[R] S) (ω : Ω[S⁄R]) :
    pullback (f.comp g) ω = pullback f (pullback g ω) := by
  induction mem_span_range ω using Submodule.span_induction with
  | mem ω hω => obtain ⟨x, rfl⟩ := hω; rw [pullback_D, pullback_D, pullback_D, AlgHom.comp_apply]
  | zero => rw [map_zero, map_zero, map_zero]
  | add ω₁ ω₂ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, ih₁, ih₂]
  | smul s ω _ ih =>
    -- The three semilinear scalar laws compose: `(f.comp g).toRingHom s` is `f (g s)`
    -- definitionally.
    rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, ih]; rfl

/-- The pullback along the identity is the identity, as (plainly linear) maps. The ascription is
what lets the elaborator compare both sides over `RingHom.id S`. -/
theorem pullback_id :
    (pullback (AlgHom.id R S) : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) = LinearMap.id :=
  LinearMap.ext pullback_id_apply

/-- Contravariant functoriality at map level; the composite's scalar law is supplied by Mathlib's
`RingHomCompTriple` instance for composed algebra maps. -/
theorem pullback_comp (f g : S →ₐ[R] S) :
    pullback (f.comp g) = (pullback f).comp (pullback g) :=
  LinearMap.ext (pullback_comp_apply f g)

end KaehlerDifferential
