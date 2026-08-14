/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on admissible changes of variables

Material complementing `Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean`: the
negation automorphism `[-1]` of a Weierstrass curve as an admissible change of variables, with
its involution API, together with the compatibility of the action with base change
(`baseChange_smul_baseChange`) and the three base-change facts that Galois descent runs on:
`smul_eq_of_baseChange_smul_eq` (a relation between base changes descends when the change of
variables does), `negVariableChange_baseChange_map` (`[-1]` is defined over the base, so a base
automorphism fixes it) and `map_smul_baseChange_eq` (the conjugate of an isomorphism of base
changes is again one). Comparing an isomorphism with its conjugate via the last of these is what
produces the Galois cocycle used by the twist classification.

That cocycle comparison lands on a product `C * [-1]`. Mathlib gives a product only as a whole
structure literal (`VariableChange.mul_def`), so this file also reads off its components:
`VariableChange.mul_u/_r/_s/_t` for an arbitrary product, and `mul_negVariableChange_u/_r/_s/_t`
for the `[-1]` case, the latter derived from the former. Only the `[-1]` four are `@[simp]`.

The negation is the nontrivial automorphism in the `Aut (E, O)`
milestone of `TauCetiRoadmap/EllipticCurves/README.md` §Layer 1, proved in
`TauCeti/AlgebraicGeometry/EllipticCurve/Aut.lean` to exhaust `Aut(E)` with the identity when
`j(E) ∉ {0, 1728}`.

Everything here is stated over a commutative ring: `⟨-1, 0, -a₁, -a₃⟩` is an admissible change
of variables for a Weierstrass curve over any commutative ring, and the two identities it
satisfies are polynomial. Only the nontriviality `negVariableChange_ne_one` needs the curve to
be elliptic over a nontrivial ring.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean` at the roadmap's pin
`bc2fe8ff7396` (FLT PR #1088), Apache 2.0, by Kevin Buzzard and Claude), generalised here from
FLT's field-level statements to a commutative ring.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (E : WeierstrassCurve R)

/-- The automorphism `[-1] : (x, y) ↦ (x, -y - a₁x - a₃)` of a Weierstrass curve, as an admissible
change of variables `⟨-1, 0, -a₁, -a₃⟩`. It fixes `E` (`negVariableChange_smul_self`) and is an
involution (`negVariableChange_mul_self`). -/
def negVariableChange : VariableChange R :=
  ⟨-1, 0, -E.a₁, -E.a₃⟩

@[simp] lemma negVariableChange_u : E.negVariableChange.u = -1 := by
  simp only [negVariableChange]

@[simp] lemma negVariableChange_r : E.negVariableChange.r = 0 := by
  simp only [negVariableChange]

@[simp] lemma negVariableChange_s : E.negVariableChange.s = -E.a₁ := by
  simp only [negVariableChange]

@[simp] lemma negVariableChange_t : E.negVariableChange.t = -E.a₃ := by
  simp only [negVariableChange]

/-- The negation automorphism fixes the curve. -/
@[simp] lemma negVariableChange_smul_self : E.negVariableChange • E = E := by
  ext <;>
    simp only [negVariableChange, variableChange_def, inv_neg, inv_one, Units.val_neg,
      Units.val_one] <;>
    ring

/-- The negation automorphism commutes with base change along a ring homomorphism. -/
@[simp] lemma negVariableChange_map {A : Type*} [CommRing A] (φ : R →+* A) :
    (E.map φ).negVariableChange = E.negVariableChange.map φ := by
  ext <;> simp [negVariableChange, VariableChange.map, map_a₁, map_a₃]

/-- The negation automorphism is nontrivial for an elliptic curve: where `2 ≠ 0` it has
`u = -1 ≠ 1`, and where `2 = 0` it has `(s, t) = (-a₁, -a₃) ≠ (0, 0)`, since an elliptic curve
over a ring in which `2 = 0` cannot have `a₁ = a₃ = 0`. -/
lemma negVariableChange_ne_one [Nontrivial R] [E.IsElliptic] : E.negVariableChange ≠ 1 := by
  intro h
  rcases eq_or_ne (2 : R) 0 with h2 | h2
  · have hs := congrArg VariableChange.s h
    have ht := congrArg VariableChange.t h
    simp only [negVariableChange, VariableChange.one_def, neg_eq_zero] at hs ht
    grind [a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero]
  · contrapose h2
    have hv : (-1 : R) = 1 := by
      simpa [VariableChange.one_def] using congrArg (fun C : VariableChange R ↦ (C.u : R)) h
    linear_combination -hv

namespace VariableChange

variable {A : Type*} [CommRing A]

/-- **A change of variables maps its inverse to the inverse of its image.** Mathlib has this as
`map_inv` for the bundled `VariableChange.mapHom`; this is the same fact in the `.map` spelling,
which is the one goals are phrased in — `rw` does not see through `mapHom φ C ≡ C.map φ`. -/
@[simp] lemma map_inv (φ : R →+* A) (C : VariableChange R) : C⁻¹.map φ = (C.map φ)⁻¹ :=
  _root_.map_inv (VariableChange.mapHom φ) C

/-- **A change of variables maps the identity to the identity**, in the `.map` spelling. The
companion of `VariableChange.map_inv`; see there for why the bundled `mapHom` form is not enough. -/
@[simp] lemma map_one (φ : R →+* A) : (1 : VariableChange R).map φ = 1 :=
  _root_.map_one (VariableChange.mapHom φ)

/-- **A change of variables maps a product to the product of the images**, in the `.map` spelling.
The companion of `VariableChange.map_inv`; see there for why the bundled `mapHom` form is not
enough. -/
@[simp] lemma map_mul (φ : R →+* A) (C D : VariableChange R) :
    (C * D).map φ = C.map φ * D.map φ :=
  _root_.map_mul (VariableChange.mapHom φ) C D

/-! ### Components of a product

Mathlib gives the composition of two changes of variables as a single structure literal,
`VariableChange.mul_def`. These read off its four components one at a time, which is the form a
goal about one component needs. Deliberately not `@[simp]`: rewriting a product to its components
is not a normal form, and doing it eagerly would undo the packaging `mul_def` provides. -/

variable (C C' : VariableChange R)

/-- The scaling factors of a composite multiply. -/
lemma mul_u : (C * C').u = C.u * C'.u := rfl

/-- The translation of a composite: the first one's, rescaled by the second's `u`, plus the
second's. -/
lemma mul_r : (C * C').r = C.r * (C'.u : R) ^ 2 + C'.r := rfl

/-- The shear of a composite: the first one's, rescaled by the second's `u`, plus the second's. -/
lemma mul_s : (C * C').s = (C'.u : R) * C.s + C'.s := rfl

/-- The `t` component of a composite, which unlike the others also mixes the first change's `r`
with the second's shear. -/
lemma mul_t : (C * C').t = C.t * (C'.u : R) ^ 3 + C.r * C'.s * (C'.u : R) ^ 2 + C'.t := rfl

end VariableChange

/-! ### Components of a change of variables composed with `[-1]`

`[-1]` has `u = -1` and `r = 0`, so composing with it on either side negates `u`, fixes `r`, and
shifts `s` and `t` by the curve's `a₁` and `a₃`. Composition is not commutative, and the two
sides differ in how the *other* change's `u` enters, so both are recorded.

These are the `VariableChange.mul_*` projections above specialised to `negVariableChange` and
simplified; unlike those, they *are* `@[simp]`, because the right-hand sides are the normal form
wanted downstream — the cocycle comparisons of the twist classification land on exactly these
products. -/

variable (C : VariableChange R)

/-- Composing with `[-1]` negates the scaling factor `u`. -/
@[simp] lemma mul_negVariableChange_u : (C * E.negVariableChange).u = -C.u := by
  rw [VariableChange.mul_u, negVariableChange_u, mul_neg, mul_one]

/-- Composing with `[-1]` leaves the translation `r` unchanged, `[-1]` having `r = 0` and
`u = -1` entering squared. -/
@[simp] lemma mul_negVariableChange_r : (C * E.negVariableChange).r = C.r := by
  rw [VariableChange.mul_r, negVariableChange_u, negVariableChange_r, Units.val_neg,
    Units.val_one, neg_one_sq, mul_one, add_zero]

/-- Composing with `[-1]` negates the shear `s` and shifts it by the curve's `a₁`. -/
@[simp] lemma mul_negVariableChange_s : (C * E.negVariableChange).s = -C.s - E.a₁ := by
  rw [VariableChange.mul_s, negVariableChange_u, negVariableChange_s, Units.val_neg,
    Units.val_one, neg_mul, one_mul, sub_eq_add_neg]

/-- Composing with `[-1]` negates the translation `t` and shifts it by `r * a₁` and the curve's
`a₃`. -/
@[simp] lemma mul_negVariableChange_t :
    (C * E.negVariableChange).t = -C.t - C.r * E.a₁ - E.a₃ := by
  rw [VariableChange.mul_t, negVariableChange_u, negVariableChange_s, negVariableChange_t,
    Units.val_neg, Units.val_one]
  ring

/-- Precomposing with `[-1]` negates the scaling factor `u`. -/
@[simp] lemma negVariableChange_mul_u : (E.negVariableChange * C).u = -C.u := by
  rw [VariableChange.mul_u, negVariableChange_u, neg_one_mul]

/-- Precomposing with `[-1]` leaves the translation `r` unchanged, `[-1]` having `r = 0`. -/
@[simp] lemma negVariableChange_mul_r : (E.negVariableChange * C).r = C.r := by
  rw [VariableChange.mul_r, negVariableChange_r, zero_mul, zero_add]

/-- Precomposing with `[-1]` shifts the shear `s` by `u * a₁`. Unlike the postcomposed
`mul_negVariableChange_s`, `s` itself is not negated: it is the *second* factor's `u` that
rescales, and here that is `C`'s rather than `-1`. -/
@[simp] lemma negVariableChange_mul_s :
    (E.negVariableChange * C).s = C.s - (C.u : R) * E.a₁ := by
  rw [VariableChange.mul_s, negVariableChange_s, mul_neg, ← sub_eq_neg_add]

/-- Precomposing with `[-1]` shifts the translation `t` by `a₃ * u ^ 3`, and contributes nothing
through `r`, which is zero for `[-1]`. -/
@[simp] lemma negVariableChange_mul_t :
    (E.negVariableChange * C).t = C.t - E.a₃ * (C.u : R) ^ 3 := by
  rw [VariableChange.mul_t, negVariableChange_r, negVariableChange_t]
  ring

/-- The negation automorphism is an involution. Each component follows from the lemmas just
above, `[-1]` being both factors. -/
@[simp] lemma negVariableChange_mul_self : E.negVariableChange * E.negVariableChange = 1 := by
  ext <;> simp [VariableChange.one_def]

/-- The negation automorphism is its own inverse, being an involution. -/
@[simp] lemma negVariableChange_inv : E.negVariableChange⁻¹ = E.negVariableChange :=
  inv_eq_of_mul_eq_one_left E.negVariableChange_mul_self

section BaseChange

variable (L : Type*) [CommRing L] [Algebra R L]

/-- **Base change commutes with the action of a change of variables.** Base changing a curve and
then acting by the base-changed variable change gives the same model as acting first and base
changing the result, so a `VariableChange`-invariant statement over `R` transports to `L`. Stated
in the `baseChange` spelling, so it rewrites directly in goals phrased that way. -/
@[simp]
lemma baseChange_smul_baseChange (C : VariableChange R) (V : WeierstrassCurve R) :
    (C.baseChange L) • V.baseChange L = (C • V).baseChange L :=
  map_variableChange (W := V) (C := C) (φ := algebraMap R L)

/-- **A relation between base changes descends, provided the change of variables does.** If `C` is
defined over `R` and `Cᴸ` carries `Vᴸ` to `Wᴸ`, then `C` already carries `V` to `W` over `R`. The
content is that base change is injective on models when `R → L` is. -/
lemma smul_eq_of_baseChange_smul_eq (hRL : Function.Injective (algebraMap R L))
    (C : VariableChange R) {V W : WeierstrassCurve R}
    (h : (C.baseChange L) • V.baseChange L = W.baseChange L) : C • V = W :=
  map_injective hRL ((baseChange_smul_baseChange L C V).symm.trans h)

/-- **The automorphism `[-1]` of a base-changed curve is defined over the base**, hence fixed by
every `R`-algebra map `L → L`: its four components `-1, 0, -a₁, -a₃` all come from `R`. -/
@[simp]
lemma negVariableChange_baseChange_map (σ : L →ₐ[R] L) :
    (E.baseChange L).negVariableChange.map (σ : L →+* L)
      = (E.baseChange L).negVariableChange := by
  have h : (E.baseChange L).map (σ : L →+* L) = E.baseChange L :=
    map_baseChange (R := R) (W := E) σ
  rw [← negVariableChange_map, h]

/-- **The conjugate of an isomorphism between base-changed curves is again one.** If
`ρ : Vᴸ ≅ Wᴸ` and `V`, `W` are defined over `R`, then `σρ` is also an isomorphism `Vᴸ ≅ Wᴸ`,
because `σ` fixes both curves. Only that `σ` is an `R`-algebra map is used, not that it is
invertible; the Galois case is the instance the twist classification takes. Comparing `ρ` with
`σρ` is what produces the Galois cocycle. -/
lemma map_smul_baseChange_eq (σ : L →ₐ[R] L) {V W : WeierstrassCurve R}
    {ρ : VariableChange L}
    (hρ : ρ • V.baseChange L = W.baseChange L) :
    (ρ.map (σ : L →+* L)) • V.baseChange L = W.baseChange L := by
  have hV : (V.baseChange L).map (σ : L →+* L) = V.baseChange L :=
    map_baseChange (R := R) (W := V) σ
  have hW : (W.baseChange L).map (σ : L →+* L) = W.baseChange L :=
    map_baseChange (R := R) (W := W) σ
  have hmv := map_variableChange (W := V.baseChange L) (C := ρ) (φ := (σ : L →+* L))
  rwa [hρ, hV, hW] at hmv

end BaseChange

end WeierstrassCurve

end
