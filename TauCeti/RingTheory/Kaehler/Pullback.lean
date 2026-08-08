/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Pullback of Kähler differentials along an algebra endomorphism

For an `R`-algebra endomorphism `f : S →ₐ[R] S`, the pullback on Kähler differentials is the map
`Ω[S⁄R] → Ω[S⁄R]` sending `D x` to `D (f x)`. It is not `S`-linear but `f`-**semilinear** —
`pullback f (s • ω) = f s • pullback f ω` — so it is packaged as a semilinear map
`Ω[S⁄R] →ₛₗ[f.toRingHom] Ω[S⁄R]`, following the precedent of `LinearMap.frobenius`.

Mathlib's `KaehlerDifferential.map` does not specialise to this: instantiating its target algebra
at `S` with the structure given by `f` would install a second `Algebra S S` instance clashing with
`Algebra.id`. Instead the map is obtained from the universal property: `x ↦ D (f x)` is a
derivation into `Ω[S⁄R]` carrying the `S`-action twisted through `f` (a private carrier below),
and `Derivation.liftKaehlerDifferential` linearises it.

## Main definitions

* `KaehlerDifferential.pullback f : Ω[S⁄R] →ₛₗ[f.toRingHom] Ω[S⁄R]`

## Main results

* `KaehlerDifferential.pullback_D`: `pullback f (D x) = D (f x)`.
* `KaehlerDifferential.pullback_id`: `pullback (AlgHom.id R S) = LinearMap.id`.
* `KaehlerDifferential.pullback_comp`: `pullback (f.comp g) = (pullback f).comp (pullback g)`.

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

/-- Private carrier: `Ω[S⁄R]` with the `S`-action twisted through `f`, so that `x ↦ D (f x)`
becomes an honest `S`-derivation into it. -/
private def Twisted (_f : S →ₐ[R] S) : Type _ := Ω[S⁄R]

private noncomputable instance (f : S →ₐ[R] S) : AddCommGroup (Twisted f) :=
  inferInstanceAs (AddCommGroup (Ω[S⁄R]))

/-- The twisted action: `s • m` is `f s • m` in `Ω[S⁄R]`. Built field-by-field rather than via
`Module.compHom`, whose `with`-merged structure does not reduce under heterogeneous `SMul` (see
the porting note on `Module.compHom` itself). -/
private noncomputable instance instSMulTwisted (f : S →ₐ[R] S) : SMul S (Twisted f) :=
  ⟨fun s m => (f s • (m : Ω[S⁄R]) : Ω[S⁄R])⟩

/-- The twisted scalar action, read in `Ω[S⁄R]`: definitional, and the single bridge every proof
below rewrites through. -/
private theorem twisted_smul_def (f : S →ₐ[R] S) (s : S) (m : Twisted f) :
    s • m = (f s • (m : Ω[S⁄R]) : Ω[S⁄R]) := rfl

/-- Addition on the twisted carrier, read in `Ω[S⁄R]`: definitional. -/
private theorem twisted_add_def (f : S →ₐ[R] S) (m n : Twisted f) :
    m + n = ((m : Ω[S⁄R]) + (n : Ω[S⁄R]) : Ω[S⁄R]) := rfl

/-- Zero on the twisted carrier, read in `Ω[S⁄R]`: definitional. -/
private theorem twisted_zero_def (f : S →ₐ[R] S) :
    (0 : Twisted f) = ((0 : Ω[S⁄R]) : Ω[S⁄R]) := rfl

private noncomputable instance (f : S →ₐ[R] S) : Module S (Twisted f) where
  one_smul m := by rw [twisted_smul_def, map_one, one_smul]
  mul_smul a b m := by
    rw [twisted_smul_def, twisted_smul_def, twisted_smul_def, map_mul, mul_smul]
  smul_zero s := by rw [twisted_smul_def, twisted_zero_def, smul_zero]
  smul_add s m n := by
    rw [twisted_smul_def, twisted_smul_def, twisted_smul_def, twisted_add_def, twisted_add_def,
      smul_add]
  add_smul a b m := by
    rw [twisted_smul_def, twisted_smul_def, twisted_smul_def, twisted_add_def, map_add, add_smul]
  zero_smul m := by rw [twisted_smul_def, twisted_zero_def, map_zero, zero_smul]

private instance (f : S →ₐ[R] S) : IsScalarTower R S (Twisted f) where
  smul_assoc r s m := by
    -- Both `R`-actions are the untwisted one; the `S`-action applies `f`, which fixes `R`.
    show (r • s) • m = r • (s • m : Twisted f)
    rw [twisted_smul_def, twisted_smul_def, Algebra.smul_def, map_mul, f.commutes,
      ← Algebra.smul_def]
    exact smul_assoc r (f s) (m : Ω[S⁄R])

/-- `x ↦ D (f x)`, as a derivation into the twisted carrier: the Leibniz rule
`D (f (a b)) = f a • D (f b) + f b • D (f a)` is exactly the twisted `S`-linearity. -/
private noncomputable def twistedD (f : S →ₐ[R] S) : Derivation R S (Twisted f) where
  toFun x := (D R S (f x) : Ω[S⁄R])
  map_add' x y := by
    change (D R S (f (x + y)) : Ω[S⁄R]) = D R S (f x) + D R S (f y)
    rw [map_add, map_add]
  map_smul' r x := by
    change (D R S (f (r • x)) : Ω[S⁄R]) = r • D R S (f x)
    rw [map_smul, Derivation.map_smul]
  map_one_eq_zero' := by
    change (D R S (f 1) : Ω[S⁄R]) = 0
    rw [map_one, Derivation.map_one_eq_zero]
  leibniz' a b := by
    change (D R S (f (a * b)) : Ω[S⁄R]) = f a • D R S (f b) + f b • D R S (f a)
    rw [map_mul, Derivation.leibniz]

/-- **Pullback of Kähler differentials along an algebra endomorphism**, characterised by
`pullback f (D x) = D (f x)`. It is `f`-semilinear: `pullback f (s • ω) = f s • pullback f ω`. -/
noncomputable def pullback (f : S →ₐ[R] S) : Ω[S⁄R] →ₛₗ[f.toRingHom] Ω[S⁄R] where
  toFun ω := ((twistedD f).liftKaehlerDifferential ω : Ω[S⁄R])
  map_add' := map_add _
  map_smul' s ω :=
    -- `S`-linearity of the lift into the twisted carrier IS `f`-semilinearity in `Ω[S⁄R]`.
    (twistedD f).liftKaehlerDifferential.map_smul s ω

@[simp]
theorem pullback_D (f : S →ₐ[R] S) (x : S) : pullback f (D R S x) = D R S (f x) :=
  (twistedD f).liftKaehlerDifferential_comp_D x

@[simp]
theorem pullback_id : pullback (AlgHom.id R S) = LinearMap.id := by
  refine LinearMap.ext_on_range (span_range_derivation R S) fun x => ?_
  simp

theorem pullback_comp (f g : S →ₐ[R] S) :
    pullback (f.comp g) = (pullback f).comp (pullback g) := by
  refine LinearMap.ext_on_range (span_range_derivation R S) fun x => ?_
  simp

end KaehlerDifferential
