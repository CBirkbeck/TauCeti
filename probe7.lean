import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Is AINTLIB `EC/AffinePointMap.lean` superseded?  It ships `map`, `map_add`, `map_neg`,
`mapAddMonoidHom`, `map_zsmul` for the point map along a ring hom. -/

open WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] (f : F →+* K) (W : WeierstrassCurve F)
  [W.toAffine.IsElliptic]

-- the bundled additive map
example : W.toAffine.Point →+ (W.map f).toAffine.Point := Affine.Point.map W f

-- additivity, negation and ℤ-scaling all come from the bundling
example (P Q : W.toAffine.Point) :
    Affine.Point.map W f (P + Q) = Affine.Point.map W f P + Affine.Point.map W f Q := by
  exact?

example (P : W.toAffine.Point) :
    Affine.Point.map W f (-P) = -Affine.Point.map W f P := by
  exact?

example (n : ℤ) (P : W.toAffine.Point) :
    Affine.Point.map W f (n • P) = n • Affine.Point.map W f P := by
  exact?
