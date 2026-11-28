import Mathlib.Algebra.Algebra.Rat
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace OMA.S_mo_151396

/-- Points on the base change of the elliptic curve, including its point at infinity. -/
abbrev CurvePoints (E : WeierstrassCurve ℚ) (K : Type) [Field K] [CharZero K] :=
  (E.toAffine.baseChange K).Point

open Classical in
/-- The map on points induced by an embedding of fields over the rationals. -/
noncomputable def pointMap (E : WeierstrassCurve ℚ)
    {K L : Type} [Field K] [CharZero K] [Field L] [CharZero L]
    (f : K →ₐ[ℚ] L) : CurvePoints E K →+ CurvePoints E L :=
  WeierstrassCurve.Affine.Point.map (W' := E.toAffine) f

/-- The underlying field automorphism of an absolute Galois group element. -/
abbrev fieldAut {K : Type} [Field K] (g : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := g

open Classical in
/-- Galois conjugation on points of the base-changed curve. -/
noncomputable def galoisAction (E : WeierstrassCurve ℚ)
    {K : Type} [Field K] [CharZero K] (g : Field.absoluteGaloisGroup K)
    (P : CurvePoints E (AlgebraicClosure K)) : CurvePoints E (AlgebraicClosure K) :=
  pointMap E
    { toRingHom := (fieldAut g).toRingEquiv.toRingHom
      commutes' := fun q => map_ratCast (fieldAut g).toRingEquiv.toRingHom q } P

abbrev Cochain (E : WeierstrassCurve ℚ) :=
  Field.absoluteGaloisGroup ℚ → CurvePoints E (AlgebraicClosure ℚ)

open Classical in
/-- A cocycle restricts to a coboundary over K for each embedding of algebraic closures.
Compatible automorphisms express the restriction from the local to the global Galois group. -/
def IsLocalCoboundary (E : WeierstrassCurve ℚ) (c : Cochain E)
    (K : Type) [Field K] [CharZero K] : Prop :=
  ∀ e : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K,
    ∃ P : CurvePoints E (AlgebraicClosure K),
    ∀ (g : Field.absoluteGaloisGroup K) (h : Field.absoluteGaloisGroup ℚ),
      (∀ x, e (fieldAut h x) = fieldAut g (e x)) →
        pointMap E e (c h) = galoisAction E g P - P

open Classical in
/-- Continuous cocycles whose classes vanish over the reals and every p-adic field.
For the discrete point group, a cocycle is continuous exactly when its zero fiber is open. -/
def LocalCocycles (E : WeierstrassCurve ℚ) : Type :=
  {c : Cochain E //
    IsOpen {g | c g = 0} ∧
      (∀ g h, c (g * h) = c g + galoisAction E g (c h)) ∧
      IsLocalCoboundary E c ℝ ∧
        ∀ (p : ℕ) (_ : Fact p.Prime), IsLocalCoboundary E c (Padic p)}

open Classical in
/-- The locally trivial Galois cohomology classes modulo global coboundaries. -/
def TateShafarevichClasses (E : WeierstrassCurve ℚ) : Type :=
  Quot fun (c d : LocalCocycles E) =>
    ∃ P : CurvePoints E (AlgebraicClosure ℚ),
      ∀ g, d.val g = c.val g + (galoisAction E g P - P)

/-- The cohomology class represented by a locally trivial cocycle. -/
def shaClass {E : WeierstrassCurve ℚ} (c : LocalCocycles E) :
    TateShafarevichClasses E :=
  Quot.mk _ c

/-- The kth Fermat number. -/
def fermatNumber (k : ℕ) : ℕ :=
  2 ^ (2 ^ k) + 1

/-- The rational curve with equation y² = x³ + d x. -/
def fermatCurve (d : ℕ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := d
  a₆ := 0

open Classical in
/-- For a prime Fermat number with k at least one, the Tate–Shafarevich group
of the corresponding curve is the product of two cyclic groups of order 2^(k-1).
Preservation of addition is expressed on cocycle representatives. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k → (fermatNumber k).Prime →
      let E := fermatCurve (fermatNumber k)
      let modulus := 2 ^ (k - 1)
      ∃ equiv : TateShafarevichClasses E ≃ ZMod modulus × ZMod modulus,
        ∀ c d : LocalCocycles E,
          ∃ sum : LocalCocycles E,
            (∀ g, sum.val g = c.val g + d.val g) ∧
            equiv (shaClass sum) = equiv (shaClass c) + equiv (shaClass d) := by
  sorry

end OMA.S_mo_151396
