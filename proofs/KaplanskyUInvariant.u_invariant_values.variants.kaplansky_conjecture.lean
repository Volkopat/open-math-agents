import FormalConjectures.Paper.KaplanskyUInvariant
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Abel
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Central.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.NormNum

/-!
# A field with u-invariant six

The final countable-tower construction comes from the accepted reduction
in Open Math Agents pull request 9836. Its source is included below for
single-file checking. The seed is the tensor product of the quaternion algebras
(−1,−1) and (2,t) over the countable field ℚ(t). Its Albert form is anisotropic
by the valuation at t and the irrationality of √2. The skew elements and a
noncommutative corner calculation prove that the tensor product is division.

We give an algebraic proof of Merkurjev's index result in the biquaternion case,
following Tignol's polynomial argument as presented by Elman, Karpenko and
Merkurjev, The Algebraic and Geometric Theory of Quadratic Forms, Chapter IV,
section 30 (Lemmas 30.1 and 30.2 and Corollary 30.9).

Extend the division algebra by five independent rational parameters. A root
of the radicand on the quadric's affine chart would successively give six
anticommuting elements with nonzero scalar squares in the original algebra.
For each parameter, a common polynomial lattice and its principal generator
conjugate all earlier roots to constants and the new root to an affine
polynomial. Comparing its coefficients supplies the next two generators.

The products of distinct generators have different characters under
conjugation, so all 64 are independent. A biquaternion algebra has dimension
16. The radicand is therefore a nonsquare in the division algebra. The
quadratic extension gives a point of the quadric and preserves division.
-/

section

/-!
# Reduction of Kaplansky's conjecture to Merkurjev's biquaternion index-preservation theorem

Kaplansky conjectured that every finite $u$-invariant of a field of characteristic not $2$ is a
power of $2$. Merkurjev disproved this by constructing a field of $u$-invariant $6$ via an
iterated tower of function fields of $7$-dimensional quadrics preserving a biquaternion division
algebra.

This reduction formalizes the complete Merkurjev tower construction in `main`: starting from a
countable field with a biquaternion division algebra (`H1`) and Merkurjev's one-step index
preservation theorem over $7$-dimensional diagonal forms (`H2`), we extract countable subfields
along an $\omega$-chain killing all $7$-dimensional forms by Cantor dovetailing, pass to the
direct limit field, show the biquaternion algebra remains a division algebra over the direct limit
(hence its $6$-dimensional Albert form is anisotropic), show every form of dimension $\ge 7$ is
isotropic, deduce `IsUInvariant 6`, and observe that $6$ is not a power of $2$.
-/

namespace OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1

open KaplanskyUInvariant QuadraticMap QuadraticForm
open scoped TensorProduct

/-- Existence of a countable field `F` of characteristic not `2` carrying a biquaternion division
algebra `QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d` (i.e., with no zero divisors),
such as `ℚ(t₁, t₂, t₃, t₄)` with `a = t₁, b = t₂, c = t₃, d = t₄`. -/
def H1 : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NeZero (2 : F)) (_ : Countable F) (a b c d : F),
    NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d)

/-- Merkurjev's index preservation theorem [Merkurjev1989]: if `QuaternionAlgebra K a 0 b ⊗[K]
QuaternionAlgebra K c 0 d` has no zero divisors over a field `K` of characteristic not `2`, then for
every `7`-dimensional diagonal quadratic form `∑ i, w i * x_i ^ 2` over `K`, there exists a field
extension `L / K` in which this `7`-dimensional form becomes isotropic while the base-changed
biquaternion algebra still has no zero divisors. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NeZero (2 : K)] (a b c d : K),
    NoZeroDivisors (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d) →
    ∀ w : Fin 7 → K,
      ∃ (L : Type) (_ : Field L) (f : K →+* L),
        (∃ v : Fin 7 → L, v ≠ 0 ∧ ∑ i : Fin 7, f (w i) * v i ^ 2 = 0) ∧
        NoZeroDivisors (QuaternionAlgebra L (f a) 0 (f b) ⊗[L] QuaternionAlgebra L (f c) 0 (f d))

lemma albert_anisotropic_of_noZeroDivisors {F : Type} [Field F] (a b c d : F)
    (hD : NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d)) :
    ∀ v : Fin 6 → F,
      a * v 0 ^ 2 + b * v 1 ^ 2 - a * b * v 2 ^ 2 -
        c * v 3 ^ 2 - d * v 4 ^ 2 + c * d * v 5 ^ 2 = 0 → v = 0 := by
  intro v hv
  let u : QuaternionAlgebra F a 0 b := ⟨0, v 0, v 1, v 2⟩
  let w : QuaternionAlgebra F c 0 d := ⟨0, v 3, v 4, v 5⟩
  have hu : u * u = algebraMap F (QuaternionAlgebra F a 0 b)
      (a * v 0 ^ 2 + b * v 1 ^ 2 - a * b * v 2 ^ 2) := by
    ext <;> simp [u, QuaternionAlgebra.algebraMap_eq] <;> ring
  have hw : w * w = algebraMap F (QuaternionAlgebra F c 0 d)
      (c * v 3 ^ 2 + d * v 4 ^ 2 - c * d * v 5 ^ 2) := by
    ext <;> simp [w, QuaternionAlgebra.algebraMap_eq] <;> ring
  let x₁ : QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d :=
    u ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) - (1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] w
  let x₂ : QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d :=
    u ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) + (1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] w
  have hmul : x₁ * x₂ = 0 := by
    have h1 : x₁ * x₂ = (u * u) ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) -
        (1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] (w * w) := by
      simp only [x₁, x₂, sub_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      abel
    rw [h1, hu, hw, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← sub_smul]
    have hcoeff : (a * v 0 ^ 2 + b * v 1 ^ 2 - a * b * v 2 ^ 2) -
        (c * v 3 ^ 2 + d * v 4 ^ 2 - c * d * v 5 ^ 2) = 0 := by
      linear_combination hv
    rw [hcoeff, zero_smul]
  let B := (QuaternionAlgebra.basisOneIJK a 0 b).tensorProduct (QuaternionAlgebra.basisOneIJK c 0 d)
  have hcoord : ∀ s : F,
      u ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) + s • ((1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] w) = 0 →
      s = 1 ∨ s = -1 → v = 0 := by
    intro s hs hpm
    have hAt : ∀ i j : Fin 4,
        B.repr (u ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) +
          s • ((1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] w)) (i, j) = 0 := fun i j => by
      rw [hs, map_zero]; rfl
    have hv0 : v 0 = 0 := by
      have h := hAt 1 0
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      simpa using h
    have hv1 : v 1 = 0 := by
      have h := hAt 2 0
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      simpa using h
    have hv2 : v 2 = 0 := by
      have h := hAt 3 0
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      simpa using h
    have hv3 : v 3 = 0 := by
      have h := hAt 0 1
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      rcases hpm with rfl | rfl <;> simpa using h
    have hv4 : v 4 = 0 := by
      have h := hAt 0 2
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      rcases hpm with rfl | rfl <;> simpa using h
    have hv5 : v 5 = 0 := by
      have h := hAt 0 3
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      rcases hpm with rfl | rfl <;> simpa using h
    funext i
    fin_cases i <;> assumption
  rcases hD.eq_zero_or_eq_zero_of_mul_eq_zero hmul with hx1 | hx2
  · exact hcoord (-1) (by simpa [x₁, sub_eq_add_neg] using hx1) (Or.inr rfl)
  · exact hcoord 1 (by simpa [x₂] using hx2) (Or.inl rfl)

lemma six_mem_anisotropicDims_of_noZeroDivisors {F : Type} [Field F] [NeZero (2 : F)]
    (a b c d : F)
    (hD : NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d)) :
    6 ∈ anisotropicDims F := by
  refine mem_anisotropicDims_iff.mpr ⟨weightedSumSquares F ![a, b, -(a * b), -c, -d, c * d], ?_⟩
  intro v hv
  simp only [weightedSumSquares_apply, Fin.sum_univ_six, smul_eq_mul] at hv
  have h0 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 0 = a := rfl
  have h1 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 1 = b := rfl
  have h2 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 2 = -(a * b) := rfl
  have h3 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 3 = -c := rfl
  have h4 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 4 = -d := rfl
  have h5 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 5 = c * d := rfl
  rw [h0, h1, h2, h3, h4, h5] at hv
  exact albert_anisotropic_of_noZeroDivisors a b c d hD v (by linear_combination hv)

lemma exists_biquat_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L) (a b c d : K) :
    ∃ φ : (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d) →+*
          (QuaternionAlgebra L (f a) 0 (f b) ⊗[L] QuaternionAlgebra L (f c) 0 (f d)),
      Function.Injective φ ∧
      ∀ x i j,
        ((QuaternionAlgebra.basisOneIJK (f a) 0 (f b)).tensorProduct
          (QuaternionAlgebra.basisOneIJK (f c) 0 (f d))).repr (φ x) (i, j) =
        f (((QuaternionAlgebra.basisOneIJK a 0 b).tensorProduct
          (QuaternionAlgebra.basisOneIJK c 0 d)).repr x (i, j)) := by
  let A_L := QuaternionAlgebra L (f a) 0 (f b) ⊗[L] QuaternionAlgebra L (f c) 0 (f d)
  letI : Algebra K A_L := Algebra.compHom A_L f
  let ψ₁ : QuaternionAlgebra K a 0 b →ₐ[K] A_L :=
    { toFun := fun q =>
        (⟨f q.1, f q.2, f q.3, f q.4⟩ : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L]
          (1 : QuaternionAlgebra L (f c) 0 (f d))
      map_one' := by
        have h1 : (⟨f (1 : QuaternionAlgebra K a 0 b).re, f (1 : QuaternionAlgebra K a 0 b).imI,
            f (1 : QuaternionAlgebra K a 0 b).imJ, f (1 : QuaternionAlgebra K a 0 b).imK⟩ :
            QuaternionAlgebra L (f a) 0 (f b)) = 1 := by
          ext <;> simp
        change _ ⊗ₜ[L] _ = (1 : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L] 1
        rw [h1]
      map_mul' := fun x y => by
        change (⟨f (x * y).1, f (x * y).2, f (x * y).3, f (x * y).4⟩ :
            QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L] 1 = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        ext <;> simp <;> ring
      map_zero' := by
        have h0 : (⟨f (0 : QuaternionAlgebra K a 0 b).re, f (0 : QuaternionAlgebra K a 0 b).imI,
            f (0 : QuaternionAlgebra K a 0 b).imJ, f (0 : QuaternionAlgebra K a 0 b).imK⟩ :
            QuaternionAlgebra L (f a) 0 (f b)) = 0 := by
          ext <;> simp
        change _ ⊗ₜ[L] _ = 0
        rw [h0, TensorProduct.zero_tmul]
      map_add' := fun x y => by
        rw [← TensorProduct.add_tmul]
        congr 1
        ext <;> simp
      commutes' := fun r => by
        change (⟨f r, f 0, f 0, f 0⟩ : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L] 1 =
          algebraMap L A_L (f r)
        have hr : (⟨f r, f 0, f 0, f 0⟩ : QuaternionAlgebra L (f a) 0 (f b)) =
            algebraMap L (QuaternionAlgebra L (f a) 0 (f b)) (f r) := by
          ext <;> simp [QuaternionAlgebra.algebraMap_eq]
        rw [hr, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
          Algebra.algebraMap_eq_smul_one]
        rfl }
  let ψ₂ : QuaternionAlgebra K c 0 d →ₐ[K] A_L :=
    { toFun := fun q =>
        (1 : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L]
          (⟨f q.1, f q.2, f q.3, f q.4⟩ : QuaternionAlgebra L (f c) 0 (f d))
      map_one' := by
        have h1 : (⟨f (1 : QuaternionAlgebra K c 0 d).re, f (1 : QuaternionAlgebra K c 0 d).imI,
            f (1 : QuaternionAlgebra K c 0 d).imJ, f (1 : QuaternionAlgebra K c 0 d).imK⟩ :
            QuaternionAlgebra L (f c) 0 (f d)) = 1 := by
          ext <;> simp
        change _ ⊗ₜ[L] _ = (1 : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L] 1
        rw [h1]
      map_mul' := fun x y => by
        change (1 : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L]
          (⟨f (x * y).1, f (x * y).2, f (x * y).3, f (x * y).4⟩ :
            QuaternionAlgebra L (f c) 0 (f d)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        ext <;> simp <;> ring
      map_zero' := by
        have h0 : (⟨f (0 : QuaternionAlgebra K c 0 d).re, f (0 : QuaternionAlgebra K c 0 d).imI,
            f (0 : QuaternionAlgebra K c 0 d).imJ, f (0 : QuaternionAlgebra K c 0 d).imK⟩ :
            QuaternionAlgebra L (f c) 0 (f d)) = 0 := by
          ext <;> simp
        change _ ⊗ₜ[L] _ = 0
        rw [h0, TensorProduct.tmul_zero]
      map_add' := fun x y => by
        rw [← TensorProduct.tmul_add]
        congr 1
        ext <;> simp
      commutes' := fun r => by
        change (1 : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L]
          (⟨f r, f 0, f 0, f 0⟩ : QuaternionAlgebra L (f c) 0 (f d)) =
          algebraMap L A_L (f r)
        have hr : (⟨f r, f 0, f 0, f 0⟩ : QuaternionAlgebra L (f c) 0 (f d)) =
            algebraMap L (QuaternionAlgebra L (f c) 0 (f d)) (f r) := by
          ext <;> simp [QuaternionAlgebra.algebraMap_eq]
        rw [hr, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          Algebra.algebraMap_eq_smul_one]
        rfl }
  have hcomm : ∀ x y, Commute (ψ₁ x) (ψ₂ y) := fun x y => by
    change ψ₁ x * ψ₂ y = ψ₂ y * ψ₁ x
    dsimp [ψ₁, ψ₂]
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, mul_one, one_mul]
  let φAlg := Algebra.TensorProduct.lift ψ₁ ψ₂ hcomm
  let φ : (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d) →+* A_L := φAlg.toRingHom
  have hrepr : ∀ x i j,
      ((QuaternionAlgebra.basisOneIJK (f a) 0 (f b)).tensorProduct
        (QuaternionAlgebra.basisOneIJK (f c) 0 (f d))).repr (φ x) (i, j) =
      f (((QuaternionAlgebra.basisOneIJK a 0 b).tensorProduct
        (QuaternionAlgebra.basisOneIJK c 0 d)).repr x (i, j)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      intro i j
      simp
    | tmul x₁ x₂ =>
      intro i j
      have htmul : φ (x₁ ⊗ₜ[K] x₂) =
          (⟨f x₁.1, f x₁.2, f x₁.3, f x₁.4⟩ : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L]
          (⟨f x₂.1, f x₂.2, f x₂.3, f x₂.4⟩ : QuaternionAlgebra L (f c) 0 (f d)) := by
        change φAlg (x₁ ⊗ₜ[K] x₂) = _
        simp only [φAlg, Algebra.TensorProduct.lift_tmul, ψ₁, ψ₂, AlgHom.coe_mk, RingHom.coe_mk,
          MonoidHom.coe_mk, OneHom.coe_mk]
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [htmul]
      simp only [Module.Basis.tensorProduct_repr_tmul_apply, QuaternionAlgebra.coe_basisOneIJK_repr,
        smul_eq_mul]
      fin_cases i <;> fin_cases j <;> simp [map_mul]
    | add x y hx hy =>
      intro i j
      simp only [map_add, Finsupp.coe_add, Pi.add_apply, hx i j, hy i j]
  refine ⟨φ, ?_, hrepr⟩
  intro x y hxy
  apply ((QuaternionAlgebra.basisOneIJK a 0 b).tensorProduct
    (QuaternionAlgebra.basisOneIJK c 0 d)).repr.injective
  ext ⟨i, j⟩
  apply f.injective
  rw [← hrepr x i j, ← hrepr y i j, hxy]

lemma noZeroDivisors_biquat_of_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L)
    (a b c d : K)
    (hL : NoZeroDivisors (QuaternionAlgebra L (f a) 0 (f b) ⊗[L] QuaternionAlgebra L (f c) 0 (f d))) :
    NoZeroDivisors (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d) := by
  obtain ⟨φ, hφ_inj, _⟩ := exists_biquat_ringHom f a b c d
  exact Function.Injective.noZeroDivisors φ hφ_inj (map_zero φ) (map_mul φ)

lemma infinite_of_noZeroDivisors_biquat {F : Type} [Field F] [NeZero (2 : F)]
    (a b c d : F)
    (hD : NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d)) :
    Infinite F := by
  by_contra hinf
  rw [not_infinite_iff_finite] at hinf
  letI : Fintype F := Fintype.ofFinite F
  classical
  have halbert := albert_anisotropic_of_noZeroDivisors a b c d hD
  have ha : a ≠ 0 := by
    intro ha0
    have h := congr_fun (halbert ![1, 0, 0, 0, 0, 0] (by simp [ha0])) 0
    exact one_ne_zero h
  have hb : b ≠ 0 := by
    intro hb0
    have h := congr_fun (halbert ![0, 1, 0, 0, 0, 0] (by simp [hb0])) 1
    exact one_ne_zero h
  have hsq : ∀ k : F, k ≠ 0 →
      Fintype.card F + 1 ≤ 2 * (Finset.univ.image (fun x : F => k * x ^ 2)).card := by
    intro k hk
    let S := Finset.univ.image (fun x : F => k * x ^ 2)
    change Fintype.card F + 1 ≤ 2 * S.card
    have h0S : (0 : F) ∈ S := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp⟩
    have hpart : Fintype.card F =
        ∑ s ∈ S, (Finset.univ.filter (fun x : F => k * x ^ 2 = s)).card := by
      have := Finset.card_eq_sum_card_fiberwise
        (f := fun x : F => k * x ^ 2) (s := Finset.univ) (t := S)
        (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))
      simpa using this
    have hfib0 : (Finset.univ.filter (fun x : F => k * x ^ 2 = 0)).card ≤ 1 := by
      have hsub : Finset.univ.filter (fun x : F => k * x ^ 2 = 0) ⊆ {0} := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_eq_zero, sq_eq_zero_iff] at hx
        simp [hx.resolve_left hk]
      exact (Finset.card_le_card hsub).trans (by simp)
    have hfib : ∀ s ∈ S.erase 0, (Finset.univ.filter (fun x : F => k * x ^ 2 = s)).card ≤ 2 := by
      intro s hs
      obtain ⟨x₀, _, hx₀⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hs)
      have hsub : Finset.univ.filter (fun x : F => k * x ^ 2 = s) ⊆ {x₀, -x₀} := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hsqeq : x ^ 2 = x₀ ^ 2 := mul_left_cancel₀ hk (hx.trans hx₀.symm)
        have := sq_eq_sq_iff_eq_or_eq_neg.mp hsqeq
        simpa using this
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    rw [hpart, ← Finset.add_sum_erase _ _ h0S]
    have hsum : ∑ s ∈ S.erase 0, (Finset.univ.filter (fun x : F => k * x ^ 2 = s)).card ≤
        ∑ _s ∈ S.erase 0, 2 := Finset.sum_le_sum hfib
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h0S] at hsum
    have hpos : 1 ≤ S.card := Finset.one_le_card.mpr ⟨0, h0S⟩
    omega
  let S₁ := Finset.univ.image (fun x : F => a * x ^ 2)
  let S₂ := Finset.univ.image (fun y : F => c - b * y ^ 2)
  have hS₁ : Fintype.card F + 1 ≤ 2 * S₁.card := hsq a ha
  have hS₂eq : S₂.card = (Finset.univ.image (fun y : F => b * y ^ 2)).card := by
    have : S₂ = (Finset.univ.image (fun y : F => b * y ^ 2)).image (fun z : F => c - z) := by
      ext z; simp [S₂]
    rw [this, Finset.card_image_of_injective _ (sub_right_injective)]
  have hS₂ : Fintype.card F + 1 ≤ 2 * S₂.card := by rw [hS₂eq]; exact hsq b hb
  have hinter : 0 < (S₁ ∩ S₂).card := by
    have hu := Finset.card_union_add_card_inter S₁ S₂
    have hle : (S₁ ∪ S₂).card ≤ Fintype.card F := Finset.card_le_univ _
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hinter
  rw [Finset.mem_inter] at hz
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz.1
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hz.2
  have h0 : a * x ^ 2 + b * y ^ 2 - a * b * 0 ^ 2 - c * 1 ^ 2 - d * 0 ^ 2 + c * d * 0 ^ 2 = 0 := by
    have : a * x ^ 2 = c - b * y ^ 2 := hx.trans hy.symm
    linear_combination this
  have hvec := halbert ![x, y, 0, 1, 0, 0] (by
    have h0' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 0 = x := rfl
    have h1' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 1 = y := rfl
    have h2' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 2 = 0 := rfl
    have h3' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 3 = 1 := rfl
    have h4' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 4 = 0 := rfl
    have h5' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 5 = 0 := rfl
    rw [h0', h1', h2', h3', h4', h5']
    exact h0)
  have h10 : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 3 = 0 := congr_fun hvec 3
  exact one_ne_zero h10

lemma countable_subfield_closure {L : Type} [Field L] {S : Set L} (hS : S.Countable) :
    Countable (Subfield.closure S) := by
  let step : Set L → Set L := fun A =>
    A ∪ ((fun p : L × L => p.1 + p.2) '' (A ×ˢ A))
      ∪ ((fun x : L => -x) '' A)
      ∪ ((fun p : L × L => p.1 * p.2) '' (A ×ˢ A))
      ∪ ((fun x : L => x⁻¹) '' A)
  let T : ℕ → Set L := fun n => Nat.rec (S ∪ ({0, 1} : Set L)) (fun _ A => step A) n
  have hT0 : (T 0).Countable := by
    change (S ∪ ({0, 1} : Set L)).Countable
    exact hS.union (by simp)
  have hstep : ∀ A : Set L, A.Countable → (step A).Countable := by
    intro A hA
    have hadd : ((fun p : L × L => p.1 + p.2) '' (A ×ˢ A)).Countable :=
      Set.Countable.image (Set.Countable.prod hA hA) _
    have hneg : ((fun x : L => -x) '' A).Countable := Set.Countable.image hA _
    have hmul : ((fun p : L × L => p.1 * p.2) '' (A ×ˢ A)).Countable :=
      Set.Countable.image (Set.Countable.prod hA hA) _
    have hinv : ((fun x : L => x⁻¹) '' A).Countable := Set.Countable.image hA _
    exact (((hA.union hadd).union hneg).union hmul).union hinv
  have hT : ∀ n, (T n).Countable := by
    intro n
    induction n with
    | zero => exact hT0
    | succ n ih =>
      change (step (T n)).Countable
      exact hstep (T n) ih
  let U : Set L := ⋃ n, T n
  have hU : U.Countable := by
    change (⋃ n, T n).Countable
    exact Set.countable_iUnion (fun n => hT n)
  have hmono : ∀ n, T n ⊆ T (n + 1) := by
    intro n
    change T n ⊆ step (T n)
    intro x hx
    simp only [step, Set.mem_union]
    tauto
  have hmono_le : ∀ {m k : ℕ}, m ≤ k → T m ⊆ T k := by
    intro m k h
    induction h with
    | refl => exact fun _ hx => hx
    | step h ih => exact ih.trans (hmono _)
  have hmemU : ∀ x ∈ S, x ∈ U := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    change x ∈ (S ∪ ({0, 1} : Set L))
    exact Or.inl hx
  have hone : (1 : L) ∈ U := by
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    change (1 : L) ∈ (S ∪ ({0, 1} : Set L))
    exact Or.inr (by simp)
  have hadd : ∀ x y : L, x ∈ U → y ∈ U → x + y ∈ U := by
    intro x y hx hy
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    have hm' : x ∈ T (max m k) := hmono_le (Nat.le_max_left _ _) hm
    have hk' : y ∈ T (max m k) := hmono_le (Nat.le_max_right _ _) hk
    refine Set.mem_iUnion.mpr ⟨max m k + 1, ?_⟩
    change x + y ∈ step (T (max m k))
    have himg : x + y ∈
        (fun p : L × L => p.1 + p.2) '' (T (max m k) ×ˢ T (max m k)) :=
      Set.mem_image_of_mem _ (Set.mk_mem_prod hm' hk')
    simp only [step, Set.mem_union]
    tauto
  have hneg : ∀ x : L, x ∈ U → -x ∈ U := by
    intro x hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨m + 1, ?_⟩
    change -x ∈ step (T m)
    have himg : -x ∈ (fun y : L => -y) '' T m := Set.mem_image_of_mem _ hm
    simp only [step, Set.mem_union]
    tauto
  have hmul : ∀ x y : L, x ∈ U → y ∈ U → x * y ∈ U := by
    intro x y hx hy
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    have hm' : x ∈ T (max m k) := hmono_le (Nat.le_max_left _ _) hm
    have hk' : y ∈ T (max m k) := hmono_le (Nat.le_max_right _ _) hk
    refine Set.mem_iUnion.mpr ⟨max m k + 1, ?_⟩
    change x * y ∈ step (T (max m k))
    have himg : x * y ∈
        (fun p : L × L => p.1 * p.2) '' (T (max m k) ×ˢ T (max m k)) :=
      Set.mem_image_of_mem _ (Set.mk_mem_prod hm' hk')
    simp only [step, Set.mem_union]
    tauto
  have hinv : ∀ x : L, x ∈ U → x⁻¹ ∈ U := by
    intro x hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨m + 1, ?_⟩
    change x⁻¹ ∈ step (T m)
    have himg : x⁻¹ ∈ (fun y : L => y⁻¹) '' T m := Set.mem_image_of_mem _ hm
    simp only [step, Set.mem_union]
    tauto
  have hSU : (Subfield.closure S : Set L) ⊆ U := by
    intro x hx
    exact Subfield.closure_induction
      (p := fun x _ => x ∈ U)
      (fun x hx => hmemU x hx) hone
      (fun x y _ _ hxU hyU => hadd x y hxU hyU)
      (fun x _ hxU => hneg x hxU)
      (fun x _ hxU => hinv x hxU)
      (fun x y _ _ hxU hyU => hmul x y hxU hyU)
      hx
  exact hU.mono hSU

lemma not_mem_anisotropicDims_of_ge_seven {F : Type} [Field F] [NeZero (2 : F)]
    (h7 : ∀ w : Fin 7 → F, ∃ v : Fin 7 → F, v ≠ 0 ∧ ∑ i : Fin 7, w i * v i ^ 2 = 0)
    {n : ℕ} (hn : 7 ≤ n) : n ∉ anisotropicDims F := by
  intro hmem
  obtain ⟨Q, hQ⟩ := mem_anisotropicDims_iff.mp hmem
  have := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hW : (weightedSumSquares F w).Anisotropic := by
    intro v hv
    have h0 : Q (e.symm v) = 0 := by
      rw [← e.map_app (e.symm v)]
      simpa using hv
    simpa using hQ _ h0
  have hm : Module.finrank F (Fin n → F) = n := by simp
  generalize Module.finrank F (Fin n → F) = m at w hW hm
  subst m
  let w7 : Fin 7 → F := fun i => w ⟨i.1, by omega⟩
  obtain ⟨v, hv0, hvsum⟩ := h7 w7
  let u : Fin n → F := fun j => if h : j.1 < 7 then v ⟨j.1, h⟩ else 0
  have hu0 : u ≠ 0 := by
    intro hu
    apply hv0
    funext i
    have h := congr_fun hu ⟨i.1, by omega⟩
    simpa [u, i.2] using h
  have huW : weightedSumSquares F w u = 0 := by
    simp only [weightedSumSquares_apply, smul_eq_mul]
    let f7 : Fin 7 → Fin n := fun i => ⟨i.1, by omega⟩
    have hf7 : Function.Injective f7 := fun i₁ i₂ h => by ext; simpa [f7] using congr_arg Fin.val h
    have hsplit : ∑ j : Fin n, w j * (u j * u j) =
        ∑ i : Fin 7, w7 i * v i ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f7))]
      · rw [Finset.sum_image (fun i₁ _ i₂ _ h => hf7 h)]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [f7, u, w7, i.2, _root_.sq]
      · intro j _ hj
        have hge : ¬ j.1 < 7 := by
          intro hlt
          exact hj (Finset.mem_image.mpr ⟨⟨j.1, hlt⟩, Finset.mem_univ _, by ext; rfl⟩)
        simp [u, hge]
    rw [hsplit, hvsum]
  exact hu0 (hW u huW)

lemma neZero_two_of_isHom {α β : Type} [Field α] [Field β] (g : α → β)
    (h1 : g 1 = 1)
    (ha : ∀ x y, g (x + y) = g x + g y)
    (hm : ∀ x y, g (x * y) = g x * g y)
    [h2K : NeZero (2 : α)] :
    NeZero (2 : β) := by
  have h11 : (1 : α) + 1 ≠ 0 := by rw [one_add_one_eq_two]; exact h2K.out
  have hu : ((1 : α) + 1) * ((1 : α) + 1)⁻¹ = 1 := mul_inv_cancel₀ h11
  refine ⟨fun h2 => ?_⟩
  have h11L : (1 : β) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  have hg1 : g (((1 : α) + 1) * ((1 : α) + 1)⁻¹) = 1 := by rw [hu, h1]
  rw [hm, ha, h1, h11L, zero_mul] at hg1
  exact zero_ne_one hg1

lemma countable_step_on_option_nat (h2 : H2)
    (instK : Field (Option ℕ))
    (h2K : letI := instK; NeZero (2 : Option ℕ))
    (a b c d : Option ℕ)
    (hDK : letI := instK; NoZeroDivisors (QuaternionAlgebra (Option ℕ) a 0 b ⊗[Option ℕ] QuaternionAlgebra (Option ℕ) c 0 d))
    (w : Fin 7 → Option ℕ) :
    ∃ (instL : Field (Option ℕ))
      (g : @RingHom (Option ℕ) (Option ℕ) instK.toNonAssocSemiring instL.toNonAssocSemiring),
      letI := instL
      (∃ v : Fin 7 → Option ℕ, v ≠ 0 ∧ ∑ i : Fin 7, g (w i) * v i ^ 2 = 0) ∧
      NoZeroDivisors (QuaternionAlgebra (Option ℕ) (g a) 0 (g b) ⊗[Option ℕ] QuaternionAlgebra (Option ℕ) (g c) 0 (g d)) := by
  obtain ⟨L, instL, f, ⟨v, hv0, hvsum⟩, hDL⟩ := @h2 (Option ℕ) instK h2K a b c d hDK w
  let S : Set L := Set.range f ∪ Set.range v
  have hS : S.Countable := (Set.countable_range f).union (Set.countable_range v)
  let L' : Subfield L := Subfield.closure S
  haveI : Countable L' := countable_subfield_closure hS
  have hf_mem : ∀ x : Option ℕ, f x ∈ L' := fun x => Subfield.subset_closure (Or.inl ⟨x, rfl⟩)
  have hv_mem : ∀ i : Fin 7, v i ∈ L' := fun i => Subfield.subset_closure (Or.inr ⟨i, rfl⟩)
  let f_sub : @RingHom (Option ℕ) L' instK.toNonAssocSemiring inferInstance := by
    letI := instK
    exact
      { toFun := fun x => ⟨f x, hf_mem x⟩
        map_one' := Subtype.ext f.map_one
        map_mul' := fun x y => Subtype.ext (f.map_mul x y)
        map_zero' := Subtype.ext f.map_zero
        map_add' := fun x y => Subtype.ext (f.map_add x y) }
  have hf_inj : Function.Injective f := by
    letI := instK
    exact f.injective
  haveI : Infinite L' := by
    refine Infinite.of_injective (fun x : Option ℕ => (⟨f x, hf_mem x⟩ : L')) ?_
    intro x y hxy
    exact hf_inj (congr_arg Subtype.val hxy)
  letI : Encodable L' := Encodable.ofCountable L'
  letI : Denumerable L' := Denumerable.ofEncodableOfInfinite L'
  let e : Option ℕ ≃ L' := (Denumerable.eqv (Option ℕ)).trans (Denumerable.eqv L').symm
  let instNext : Field (Option ℕ) := e.field
  let j : @RingHom (Option ℕ) L instNext.toNonAssocSemiring instL.toNonAssocSemiring := by
    letI := instNext
    exact
      { toFun := fun x => (e x : L)
        map_one' := by
          change (e (e.symm 1) : L) = 1
          rw [e.apply_symm_apply]; rfl
        map_mul' := fun x y => by
          change (e (e.symm (e x * e y)) : L) = (e x : L) * (e y : L)
          rw [e.apply_symm_apply]; rfl
        map_zero' := by
          change (e (e.symm 0) : L) = 0
          rw [e.apply_symm_apply]; rfl
        map_add' := fun x y => by
          change (e (e.symm (e x + e y)) : L) = (e x : L) + (e y : L)
          rw [e.apply_symm_apply]; rfl }
  let e_symm_hom : @RingHom L' (Option ℕ) inferInstance instNext.toNonAssocSemiring := by
    letI := instNext
    exact
      { toFun := e.symm
        map_one' := rfl
        map_mul' := fun x y => by
          change e.symm (x * y) = e.symm (e (e.symm x) * e (e.symm y))
          rw [e.apply_symm_apply, e.apply_symm_apply]
        map_zero' := rfl
        map_add' := fun x y => by
          change e.symm (x + y) = e.symm (e (e.symm x) + e (e.symm y))
          rw [e.apply_symm_apply, e.apply_symm_apply] }
  let g : @RingHom (Option ℕ) (Option ℕ) instK.toNonAssocSemiring instNext.toNonAssocSemiring :=
    @RingHom.comp (Option ℕ) L' (Option ℕ) instK.toNonAssocSemiring inferInstance
      instNext.toNonAssocSemiring e_symm_hom f_sub
  have hjg : ∀ x, j (g x) = f x := fun x => by
    change (e (e.symm ⟨f x, hf_mem x⟩) : L) = f x
    rw [e.apply_symm_apply]
  refine ⟨instNext, g, ?_, ?_⟩
  · letI := instNext
    let v' : Fin 7 → Option ℕ := fun i => e.symm ⟨v i, hv_mem i⟩
    have hjv : ∀ i, j (v' i) = v i := fun i => by
      change (e (e.symm ⟨v i, hv_mem i⟩) : L) = v i
      rw [e.apply_symm_apply]
    refine ⟨v', ?_, ?_⟩
    · intro hv'0
      apply hv0
      funext i
      rw [← hjv i, congr_fun hv'0 i]
      exact j.map_zero
    · apply j.injective
      rw [map_sum, map_zero]
      convert hvsum using 2 with i
      rw [map_mul, map_pow, hjg, hjv]
  · letI := instNext
    have hDL' : NoZeroDivisors
        (QuaternionAlgebra L (j (g a)) 0 (j (g b)) ⊗[L] QuaternionAlgebra L (j (g c)) 0 (j (g d))) := by
      rw [hjg, hjg, hjg, hjg]
      exact hDL
    exact noZeroDivisors_biquat_of_ringHom j (g a) (g b) (g c) (g d) hDL'

lemma exists_tower_of_hyps (h1 : H1) (h2 : H2) :
    ∃ (G : ℕ → Type) (_ : ∀ n, Field (G n))
      (trans : ∀ i j, i ≤ j → G i →+* G j)
      (_ : DirectedSystem G (fun i j h => trans i j h))
      (a b c d : G 0),
      NeZero (2 : G 0) ∧
      (∀ n, NoZeroDivisors
        (QuaternionAlgebra (G n) (trans 0 n (Nat.zero_le n) a) 0 (trans 0 n (Nat.zero_le n) b) ⊗[G n]
         QuaternionAlgebra (G n) (trans 0 n (Nat.zero_le n) c) 0 (trans 0 n (Nat.zero_le n) d))) ∧
      (∀ (i : ℕ) (w : Fin 7 → G i), ∃ (m : ℕ) (him : i ≤ m) (v : Fin 7 → G m),
        v ≠ 0 ∧ ∑ r : Fin 7, trans i m him (w r) * v r ^ 2 = 0) := by
  obtain ⟨F₀, instF₀, h2₀, hC₀, a₀, b₀, c₀, d₀, hD₀⟩ := h1
  haveI : Infinite F₀ := infinite_of_noZeroDivisors_biquat a₀ b₀ c₀ d₀ hD₀
  letI : Encodable F₀ := Encodable.ofCountable F₀
  letI : Denumerable F₀ := Denumerable.ofEncodableOfInfinite F₀
  let e₀ : Option ℕ ≃ F₀ := (Denumerable.eqv (Option ℕ)).trans (Denumerable.eqv F₀).symm
  let inst₀ : Field (Option ℕ) := e₀.field
  let j₀ : @RingHom (Option ℕ) F₀ inst₀.toNonAssocSemiring instF₀.toNonAssocSemiring :=
    { toFun := fun x => e₀ x
      map_one' := e₀.apply_symm_apply 1
      map_mul' := fun x y => e₀.apply_symm_apply (e₀ x * e₀ y)
      map_zero' := e₀.apply_symm_apply 0
      map_add' := fun x y => e₀.apply_symm_apply (e₀ x + e₀ y) }
  let a' : Option ℕ := e₀.symm a₀
  let b' : Option ℕ := e₀.symm b₀
  let c' : Option ℕ := e₀.symm c₀
  let d' : Option ℕ := e₀.symm d₀
  have hj₀a : j₀ a' = a₀ := e₀.apply_symm_apply a₀
  have hj₀b : j₀ b' = b₀ := e₀.apply_symm_apply b₀
  have hj₀c : j₀ c' = c₀ := e₀.apply_symm_apply c₀
  have hj₀d : j₀ d' = d₀ := e₀.apply_symm_apply d₀
  have h2₀' : letI := inst₀; NeZero (2 : Option ℕ) := by
    letI := inst₀
    refine ⟨fun h => ?_⟩
    have := congr_arg j₀ h
    rw [map_ofNat, map_zero] at this
    exact NeZero.ne (2 : F₀) this
  have hD₀' : letI := inst₀
      NoZeroDivisors (QuaternionAlgebra (Option ℕ) a' 0 b' ⊗[Option ℕ] QuaternionAlgebra (Option ℕ) c' 0 d') := by
    letI := inst₀
    have hDL : NoZeroDivisors
        (QuaternionAlgebra F₀ (j₀ a') 0 (j₀ b') ⊗[F₀] QuaternionAlgebra F₀ (j₀ c') 0 (j₀ d')) := by
      rw [hj₀a, hj₀b, hj₀c, hj₀d]
      exact hD₀
    exact noZeroDivisors_biquat_of_ringHom j₀ a' b' c' d' hDL
  obtain ⟨enum7, henum7⟩ := exists_surjective_nat (Fin 7 → Option ℕ)
  -- Helper: iterate a sequence of bare functions `steps : ℕ → Option ℕ → Option ℕ` from `i` to `j`.
  let iter (steps : ℕ → Option ℕ → Option ℕ) (i j : ℕ) : Option ℕ → Option ℕ :=
    Nat.rec id (fun k acc => steps (i + k) ∘ acc) (j - i)
  have hiter_self : ∀ steps i x, iter steps i i x = x := fun steps i x => by
    simp [iter]
  have hiter_succ : ∀ steps i j, i ≤ j → ∀ x,
      iter steps i (j + 1) x = steps j (iter steps i j x) := fun steps i j hij x => by
    have hsub : j + 1 - i = (j - i) + 1 := by omega
    have hadd : i + (j - i) = j := by omega
    simp only [iter, hsub, Function.comp_apply, hadd]
  have hiter_congr : ∀ steps₁ steps₂ n, (∀ k < n, steps₁ k = steps₂ k) →
      ∀ i j, i ≤ j → j ≤ n → ∀ x, iter steps₁ i j x = iter steps₂ i j x := by
    intro steps₁ steps₂ n hagree i j hij hjn
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      subst hi; intro x; simp [hiter_self]
    | succ j ih =>
      rcases eq_or_lt_of_le hij with rfl | hlt
      · intro x; simp [hiter_self]
      · have hij' : i ≤ j := by omega
        intro x
        rw [hiter_succ _ i j hij', hiter_succ _ i j hij', hagree j (by omega),
          ih hij' (by omega)]
  have hiter_comp : ∀ steps i j k, i ≤ j → j ≤ k → ∀ x,
      iter steps j k (iter steps i j x) = iter steps i k x := by
    intro steps i j k hij hjk
    induction k with
    | zero =>
      have hj : j = 0 := by omega
      have hi : i = 0 := by omega
      subst hi; subst hj; intro x; simp [hiter_self]
    | succ k ih =>
      rcases eq_or_lt_of_le hjk with rfl | hlt
      · intro x; simp [hiter_self]
      · have hjk' : j ≤ k := by omega
        intro x
        rw [hiter_succ _ j k hjk', hiter_succ _ i k (by omega), ih hjk']
  let IsHom (iK iL : Field (Option ℕ)) (g : Option ℕ → Option ℕ) : Prop :=
    g (@Zero.zero _ iK.toZero) = @Zero.zero _ iL.toZero ∧
    g (@One.one _ iK.toOne) = @One.one _ iL.toOne ∧
    (∀ x y, g (@HAdd.hAdd _ _ _ (@instHAdd _ iK.toAdd) x y) =
      @HAdd.hAdd _ _ _ (@instHAdd _ iL.toAdd) (g x) (g y)) ∧
    (∀ x y, g (@HMul.hMul _ _ _ (@instHMul _ iK.toMul) x y) =
      @HMul.hMul _ _ _ (@instHMul _ iL.toMul) (g x) (g y))
  have hiter_hom : ∀ (insts : ℕ → Field (Option ℕ)) (steps : ℕ → Option ℕ → Option ℕ) n,
      (∀ k < n, IsHom (insts k) (insts (k + 1)) (steps k)) →
      ∀ i j, i ≤ j → j ≤ n → IsHom (insts i) (insts j) (iter steps i j) := by
    intro insts steps n hhom i j hij hjn
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      subst hi
      refine ⟨hiter_self steps 0 _, hiter_self steps 0 _, fun x y => by simp [hiter_self],
        fun x y => by simp [hiter_self]⟩
    | succ j ih =>
      rcases eq_or_lt_of_le hij with rfl | hlt
      · refine ⟨hiter_self steps (j + 1) _, hiter_self steps (j + 1) _,
          fun x y => by simp [hiter_self], fun x y => by simp [hiter_self]⟩
      · have hij' : i ≤ j := by omega
        obtain ⟨h0a, h1a, hadda, hmula⟩ := ih hij' (by omega)
        obtain ⟨h0b, h1b, haddb, hmulb⟩ := hhom j (by omega)
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hiter_succ steps i j hij', h0a, h0b]
        · rw [hiter_succ steps i j hij', h1a, h1b]
        · intro x y; rw [hiter_succ steps i j hij', hadda, haddb, ← hiter_succ steps i j hij',
            ← hiter_succ steps i j hij']
        · intro x y; rw [hiter_succ steps i j hij', hmula, hmulb, ← hiter_succ steps i j hij',
            ← hiter_succ steps i j hij']
  let Valid (n : ℕ) (insts : ℕ → Field (Option ℕ)) (steps : ℕ → Option ℕ → Option ℕ) : Prop :=
    insts 0 = inst₀ ∧
    (∀ k < n, IsHom (insts k) (insts (k + 1)) (steps k)) ∧
    (∀ k ≤ n, letI := insts k
      NoZeroDivisors
        (QuaternionAlgebra (Option ℕ) (iter steps 0 k a') 0 (iter steps 0 k b') ⊗[Option ℕ]
         QuaternionAlgebra (Option ℕ) (iter steps 0 k c') 0 (iter steps 0 k d'))) ∧
    (∀ m < n, letI := insts (m + 1)
      ∃ v : Fin 7 → Option ℕ, v ≠ 0 ∧
        ∑ r : Fin 7, iter steps (Nat.unpair m).1 (m + 1) (enum7 (Nat.unpair m).2 r) * v r ^ 2 = 0)
  have hstep : ∀ n (p : { p : (ℕ → Field (Option ℕ)) × (ℕ → Option ℕ → Option ℕ) // Valid n p.1 p.2 }),
      ∃ q : { p : (ℕ → Field (Option ℕ)) × (ℕ → Option ℕ → Option ℕ) // Valid (n + 1) p.1 p.2 },
        (∀ k ≤ n, q.val.1 k = p.val.1 k) ∧ (∀ k < n, q.val.2 k = p.val.2 k) := by
    intro n ⟨⟨insts, steps⟩, h0eq, hhom, hdiv, hiso⟩
    dsimp only at h0eq hhom hdiv hiso
    have h2n : letI := insts n; NeZero (2 : Option ℕ) := by
      obtain ⟨_, ho, ha, hm⟩ := hiter_hom insts steps n hhom 0 n (Nat.zero_le n) le_rfl
      have h20 : letI := insts 0; NeZero (2 : Option ℕ) := by rw [h0eq]; exact h2₀'
      exact @neZero_two_of_isHom (Option ℕ) (Option ℕ) (insts 0) (insts n)
        (iter steps 0 n) ho ha hm h20
    let i := (Nat.unpair n).1
    let j := (Nat.unpair n).2
    have hin : i ≤ n := Nat.unpair_left_le n
    let w : Fin 7 → Option ℕ := fun r => iter steps i n (enum7 j r)
    have hspec := countable_step_on_option_nat h2 (insts n) h2n
      (iter steps 0 n a') (iter steps 0 n b') (iter steps 0 n c') (iter steps 0 n d')
      (hdiv n le_rfl) w
    let instNext := Classical.choose hspec
    let g := Classical.choose (Classical.choose_spec hspec)
    have hg_spec := Classical.choose_spec (Classical.choose_spec hspec)
    let insts' := Function.update insts (n + 1) instNext
    let steps' := Function.update steps n (g : Option ℕ → Option ℕ)
    have hinsts_le : ∀ k ≤ n, insts' k = insts k := fun k hk =>
      Function.update_of_ne (by omega) _ _
    have hsteps_lt : ∀ k < n, steps' k = steps k := fun k hk =>
      Function.update_of_ne (by omega) _ _
    have hiter_eq : ∀ u v, u ≤ v → v ≤ n → ∀ x, iter steps' u v x = iter steps u v x :=
      hiter_congr steps' steps n hsteps_lt
    have hvalid' : Valid (n + 1) insts' steps' := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hinsts_le 0 (Nat.zero_le n), h0eq]
      · intro k hk
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with hkn | hlt
        · subst k
          rw [hinsts_le n le_rfl]
          have h1 : insts' (n + 1) = instNext := Function.update_self (n + 1) instNext insts
          have h2 : steps' n = (g : Option ℕ → Option ℕ) := Function.update_self n _ steps
          rw [h1, h2]
          exact ⟨g.map_zero, g.map_one, g.map_add, g.map_mul⟩
        · rw [hinsts_le k (by omega), hinsts_le (k + 1) (by omega), hsteps_lt k hlt]
          exact hhom k hlt
      · intro k hk
        rcases eq_or_lt_of_le hk with hkn | hlt
        · subst k
          have h1 : insts' (n + 1) = instNext := Function.update_self (n + 1) instNext insts
          have h2 : steps' n = (g : Option ℕ → Option ℕ) := Function.update_self n _ steps
          have hstep_a : iter steps' 0 (n + 1) a' = g (iter steps 0 n a') := by
            rw [hiter_succ steps' 0 n (Nat.zero_le n), h2, hiter_eq 0 n (Nat.zero_le n) le_rfl]
          have hstep_b : iter steps' 0 (n + 1) b' = g (iter steps 0 n b') := by
            rw [hiter_succ steps' 0 n (Nat.zero_le n), h2, hiter_eq 0 n (Nat.zero_le n) le_rfl]
          have hstep_c : iter steps' 0 (n + 1) c' = g (iter steps 0 n c') := by
            rw [hiter_succ steps' 0 n (Nat.zero_le n), h2, hiter_eq 0 n (Nat.zero_le n) le_rfl]
          have hstep_d : iter steps' 0 (n + 1) d' = g (iter steps 0 n d') := by
            rw [hiter_succ steps' 0 n (Nat.zero_le n), h2, hiter_eq 0 n (Nat.zero_le n) le_rfl]
          rw [hstep_a, hstep_b, hstep_c, hstep_d, h1]
          exact hg_spec.2
        · have hk' : k ≤ n := by omega
          rw [hinsts_le k hk', hiter_eq 0 k (Nat.zero_le k) hk', hiter_eq 0 k (Nat.zero_le k) hk',
            hiter_eq 0 k (Nat.zero_le k) hk', hiter_eq 0 k (Nat.zero_le k) hk']
          exact hdiv k hk'
      · intro m hm
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hm) with hmn | hlt
        · subst m
          have h1 : insts' (n + 1) = instNext := Function.update_self (n + 1) instNext insts
          have h2 : steps' n = (g : Option ℕ → Option ℕ) := Function.update_self n _ steps
          rw [h1]
          obtain ⟨v, hv0, hvsum⟩ := hg_spec.1
          refine ⟨v, hv0, ?_⟩
          have hterms : ∀ r : Fin 7,
              iter steps' (Nat.unpair n).1 (n + 1) (enum7 (Nat.unpair n).2 r) = g (w r) := by
            intro r
            change iter steps' i (n + 1) (enum7 j r) = g (iter steps i n (enum7 j r))
            rw [hiter_succ steps' i n hin, h2, hiter_eq i n hin le_rfl]
          have hsum :
              (letI := instNext
                ∑ r : Fin 7, iter steps' (Nat.unpair n).1 (n + 1) (enum7 (Nat.unpair n).2 r) * v r ^ 2) =
              (letI := instNext
                ∑ r : Fin 7, g (w r) * v r ^ 2) :=
            Finset.sum_congr rfl fun r _ => by rw [hterms r]
          rw [hsum]
          exact hvsum
        · have hmu : (Nat.unpair m).1 ≤ m := Nat.unpair_left_le m
          rw [hinsts_le (m + 1) (by omega)]
          obtain ⟨v, hv0, hvsum⟩ := hiso m hlt
          refine ⟨v, hv0, ?_⟩
          have hterms : ∀ r : Fin 7,
              iter steps' (Nat.unpair m).1 (m + 1) (enum7 (Nat.unpair m).2 r) =
              iter steps (Nat.unpair m).1 (m + 1) (enum7 (Nat.unpair m).2 r) := fun r =>
            hiter_eq (Nat.unpair m).1 (m + 1) (by omega) (by omega) _
          have hsum :
              letI := insts (m + 1)
              ∑ r : Fin 7, iter steps' (Nat.unpair m).1 (m + 1) (enum7 (Nat.unpair m).2 r) * v r ^ 2 =
              ∑ r : Fin 7, iter steps (Nat.unpair m).1 (m + 1) (enum7 (Nat.unpair m).2 r) * v r ^ 2 := by
            letI := insts (m + 1)
            exact Finset.sum_congr rfl fun r _ => by rw [hterms r]
          rw [hsum]
          exact hvsum
    exact ⟨⟨⟨insts', steps'⟩, hvalid'⟩, hinsts_le, hsteps_lt⟩
  have hbase : Valid 0 (fun _ => inst₀) (fun _ => id) := by
    refine ⟨rfl, fun k hk => by omega, ?_, fun m hm => by omega⟩
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact hD₀'
  let stepRec : ∀ n,
      { p : (ℕ → Field (Option ℕ)) × (ℕ → Option ℕ → Option ℕ) // Valid n p.1 p.2 } →
      { p : (ℕ → Field (Option ℕ)) × (ℕ → Option ℕ → Option ℕ) // Valid (n + 1) p.1 p.2 } :=
    fun n p => Classical.choose (hstep n p)
  let P : ∀ n, { p : (ℕ → Field (Option ℕ)) × (ℕ → Option ℕ → Option ℕ) // Valid n p.1 p.2 } :=
    fun n => Nat.rec ⟨⟨fun _ => inst₀, fun _ => id⟩, hbase⟩ stepRec n
  have hP_inst_step : ∀ n k, k ≤ n → (P (n + 1)).val.1 k = (P n).val.1 k := fun n k hk =>
    (Classical.choose_spec (hstep n (P n))).1 k hk
  have hP_steps_step : ∀ n k, k < n → (P (n + 1)).val.2 k = (P n).val.2 k := fun n k hk =>
    (Classical.choose_spec (hstep n (P n))).2 k hk
  have hP_inst_stable : ∀ k n, k ≤ n → (P n).val.1 k = (P k).val.1 k := by
    intro k n hkn
    induction n with
    | zero =>
      have hk : k = 0 := by omega
      subst hk
      rfl
    | succ n ih =>
      rcases eq_or_lt_of_le hkn with rfl | hlt
      · rfl
      · rw [hP_inst_step n k (by omega), ih (by omega)]
  have hP_steps_stable : ∀ k n, k < n → (P n).val.2 k = (P (k + 1)).val.2 k := by
    intro k n hkn
    induction n with
    | zero => omega
    | succ n ih =>
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hkn) with rfl | hlt
      · rfl
      · rw [hP_steps_step n k hlt, ih hlt]
  let F_inst : ℕ → Field (Option ℕ) := fun k => (P k).val.1 k
  let F_step : ℕ → Option ℕ → Option ℕ := fun k => (P (k + 1)).val.2 k
  have hF_step_hom : ∀ k, IsHom (F_inst k) (F_inst (k + 1)) (F_step k) := fun k => by
    have h := (P (k + 1)).property.2.1 k (Nat.lt_succ_self k)
    rw [hP_inst_stable k (k + 1) (Nat.le_succ k)] at h
    exact h
  have hF_iter_eq : ∀ n i j, i ≤ j → j ≤ n → ∀ x,
      iter F_step i j x = iter (P n).val.2 i j x := fun n i j hij hjn =>
    hiter_congr F_step (P n).val.2 n (fun k hk => (hP_steps_stable k n hk).symm) i j hij hjn
  -- Wrap each stage as a distinct type `G n` so `Field (G n)` synthesizes cleanly.
  let G : ℕ → Type := fun n => { _x : Option ℕ // n = n }
  let eG : ∀ n, G n ≃ Option ℕ := fun n =>
    { toFun := Subtype.val, invFun := fun x => ⟨x, rfl⟩,
      left_inv := fun ⟨_, _⟩ => rfl, right_inv := fun _ => rfl }
  let instG : ∀ n, Field (G n) := fun n => @Equiv.field (G n) (Option ℕ) (eG n) (F_inst n)
  letI : ∀ n, Field (G n) := instG
  let trans : ∀ i j, i ≤ j → G i →+* G j := fun i j hij =>
    have hhom := hiter_hom F_inst F_step j (fun k _ => hF_step_hom k) i j hij le_rfl
    { toFun := fun x => ⟨iter F_step i j x.val, rfl⟩
      map_one' := Subtype.ext hhom.2.1
      map_mul' := fun x y => Subtype.ext (hhom.2.2.2 x.val y.val)
      map_zero' := Subtype.ext hhom.1
      map_add' := fun x y => Subtype.ext (hhom.2.2.1 x.val y.val) }
  have hsys : DirectedSystem G (fun i j h => trans i j h) :=
    { map_self := fun i x => Subtype.ext (hiter_self F_step i x.val)
      map_map := by
        intro i j k h1 h2 x
        first
        | exact Subtype.ext (hiter_comp F_step _ _ _ h1 h2 x.val)
        | exact Subtype.ext (hiter_comp F_step _ _ _ h2 h1 x.val) }
  let heG_hom : ∀ n, @RingHom (G n) (Option ℕ) (instG n).toNonAssocSemiring (F_inst n).toNonAssocSemiring :=
    fun n => by
      letI := F_inst n
      exact
        { toFun := fun x => x.val
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
  refine ⟨G, instG, trans, hsys, ⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩, ?_, ?_, ?_⟩
  · have h0eq : F_inst 0 = inst₀ := (P 0).property.1
    have h2F0 : letI := F_inst 0; NeZero (2 : Option ℕ) := by rw [h0eq]; exact h2₀'
    letI := F_inst 0
    refine ⟨fun h => ?_⟩
    have hv := congr_arg (heG_hom 0) h
    rw [map_ofNat, map_zero] at hv
    exact h2F0.out hv
  · intro n
    have hDn := (P n).property.2.2.1 n le_rfl
    have heq_a : heG_hom n (trans 0 n (Nat.zero_le n) ⟨a', rfl⟩) = iter (P n).val.2 0 n a' :=
      hF_iter_eq n 0 n (Nat.zero_le n) le_rfl a'
    have heq_b : heG_hom n (trans 0 n (Nat.zero_le n) ⟨b', rfl⟩) = iter (P n).val.2 0 n b' :=
      hF_iter_eq n 0 n (Nat.zero_le n) le_rfl b'
    have heq_c : heG_hom n (trans 0 n (Nat.zero_le n) ⟨c', rfl⟩) = iter (P n).val.2 0 n c' :=
      hF_iter_eq n 0 n (Nat.zero_le n) le_rfl c'
    have heq_d : heG_hom n (trans 0 n (Nat.zero_le n) ⟨d', rfl⟩) = iter (P n).val.2 0 n d' :=
      hF_iter_eq n 0 n (Nat.zero_le n) le_rfl d'
    have hDn' : letI := F_inst n
        NoZeroDivisors
          (QuaternionAlgebra (Option ℕ) (heG_hom n (trans 0 n (Nat.zero_le n) ⟨a', rfl⟩)) 0
            (heG_hom n (trans 0 n (Nat.zero_le n) ⟨b', rfl⟩)) ⊗[Option ℕ]
           QuaternionAlgebra (Option ℕ) (heG_hom n (trans 0 n (Nat.zero_le n) ⟨c', rfl⟩)) 0
            (heG_hom n (trans 0 n (Nat.zero_le n) ⟨d', rfl⟩))) := by
      rw [heq_a, heq_b, heq_c, heq_d]
      exact hDn
    exact @noZeroDivisors_biquat_of_ringHom (G n) (Option ℕ) (instG n) (F_inst n)
      (heG_hom n) _ _ _ _ hDn'
  · intro i w
    obtain ⟨j, hj⟩ := henum7 (fun r => (w r).val)
    let m0 := Nat.pair i j
    have him0 : i ≤ m0 := by
      have := Nat.unpair_left_le m0
      simpa [m0, Nat.unpair_pair] using this
    have hiso_m := (P (m0 + 1)).property.2.2.2 m0 (Nat.lt_succ_self m0)
    simp only [m0, Nat.unpair_pair, hj] at hiso_m
    obtain ⟨v, hv0, hvsum⟩ := hiso_m
    refine ⟨m0 + 1, by omega, fun r => ⟨v r, rfl⟩, ?_, ?_⟩
    · intro hv'
      apply hv0
      funext r
      exact congr_arg Subtype.val (congr_fun hv' r)
    · letI := F_inst (m0 + 1)
      apply (heG_hom (m0 + 1)).injective
      rw [map_sum, map_zero]
      have hterms : ∀ r : Fin 7,
          heG_hom (m0 + 1) (trans i (m0 + 1) (by omega) (w r) * (⟨v r, rfl⟩ : G (m0 + 1)) ^ 2) =
          iter (P (m0 + 1)).val.2 i (m0 + 1) (w r).val * v r ^ 2 := fun r => by
        rw [map_mul, map_pow]
        congr 1
        exact hF_iter_eq (m0 + 1) i (m0 + 1) (by omega) le_rfl (w r).val
      rw [Finset.sum_congr rfl fun r _ => hterms r]
      exact hvsum

lemma isUInvariant_six_of_tower
    (G : ℕ → Type) [∀ n, Field (G n)]
    (trans : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h => trans i j h)]
    (a b c d : G 0) [NeZero (2 : G 0)]
    (hdiv : ∀ n, NoZeroDivisors
      (QuaternionAlgebra (G n) (trans 0 n (Nat.zero_le n) a) 0 (trans 0 n (Nat.zero_le n) b) ⊗[G n]
       QuaternionAlgebra (G n) (trans 0 n (Nat.zero_le n) c) 0 (trans 0 n (Nat.zero_le n) d)))
    (hiso : ∀ (i : ℕ) (w : Fin 7 → G i), ∃ (m : ℕ) (him : i ≤ m) (v : Fin 7 → G m),
      v ≠ 0 ∧ ∑ r : Fin 7, trans i m him (w r) * v r ^ 2 = 0) :
    IsUInvariant 6 := by
  let FLim : Type := DirectLimit G trans
  let of : ∀ n, G n →+* FLim := fun n => DirectLimit.Ring.of G trans n
  haveI h2Lim : NeZero (2 : FLim) := by
    refine ⟨fun h => ?_⟩
    have h' : of 0 2 = of 0 0 := by rw [map_ofNat, map_zero]; exact h
    exact NeZero.ne (2 : G 0) ((of 0).injective h')
  have hlift : ∀ {ι : Type} [Fintype ι] (u : ι → FLim),
      ∃ (N : ℕ) (uN : ι → G N), ∀ t, of N (uN t) = u t := by
    intro ι _ u
    choose idx val hval using fun t => DirectLimit.exists_eq_mk trans (u t)
    let N := Finset.univ.sup idx
    refine ⟨N, fun t => trans (idx t) N (Finset.le_sup (Finset.mem_univ t)) (val t), fun t => ?_⟩
    change DirectLimit.Ring.of G trans N _ = u t
    rw [DirectLimit.Ring.of_f]
    exact (hval t).symm
  let aLim : FLim := of 0 a
  let bLim : FLim := of 0 b
  let cLim : FLim := of 0 c
  let dLim : FLim := of 0 d
  have hDLim : NoZeroDivisors
      (QuaternionAlgebra FLim aLim 0 bLim ⊗[FLim] QuaternionAlgebra FLim cLim 0 dLim) := by
    refine ⟨fun {x y} hxy => ?_⟩
    let BLim := (QuaternionAlgebra.basisOneIJK aLim 0 bLim).tensorProduct
      (QuaternionAlgebra.basisOneIJK cLim 0 dLim)
    let u : (Fin 4 × Fin 4) ⊕ (Fin 4 × Fin 4) → FLim :=
      Sum.elim (fun p => BLim.repr x p) (fun p => BLim.repr y p)
    obtain ⟨N, uN, huN⟩ := hlift u
    let aN := trans 0 N (Nat.zero_le N) a
    let bN := trans 0 N (Nat.zero_le N) b
    let cN := trans 0 N (Nat.zero_le N) c
    let dN := trans 0 N (Nat.zero_le N) d
    have haN : of N aN = aLim := DirectLimit.Ring.of_f (G := G) (f := trans) (Nat.zero_le N) a
    have hbN : of N bN = bLim := DirectLimit.Ring.of_f (G := G) (f := trans) (Nat.zero_le N) b
    have hcN : of N cN = cLim := DirectLimit.Ring.of_f (G := G) (f := trans) (Nat.zero_le N) c
    have hdN : of N dN = dLim := DirectLimit.Ring.of_f (G := G) (f := trans) (Nat.zero_le N) d
    let BN := (QuaternionAlgebra.basisOneIJK aN 0 bN).tensorProduct
      (QuaternionAlgebra.basisOneIJK cN 0 dN)
    let xN := BN.repr.symm (Finsupp.equivFunOnFinite.symm (fun p => uN (Sum.inl p)))
    let yN := BN.repr.symm (Finsupp.equivFunOnFinite.symm (fun p => uN (Sum.inr p)))
    have hmap := exists_biquat_ringHom (of N) aN bN cN dN
    rw [haN, hbN, hcN, hdN] at hmap
    obtain ⟨φN, hφN_inj, hφN_repr⟩ := hmap
    have hxN : φN xN = x := by
      apply BLim.repr.injective
      ext ⟨i, j⟩
      rw [hφN_repr xN i j]
      have hcoord : BN.repr xN (i, j) = uN (Sum.inl (i, j)) := by
        simp [xN]
      rw [hcoord, huN (Sum.inl (i, j))]
      rfl
    have hyN : φN yN = y := by
      apply BLim.repr.injective
      ext ⟨i, j⟩
      rw [hφN_repr yN i j]
      have hcoord : BN.repr yN (i, j) = uN (Sum.inr (i, j)) := by
        simp [yN]
      rw [hcoord, huN (Sum.inr (i, j))]
      rfl
    have hmulN : xN * yN = 0 := by
      apply hφN_inj
      rw [map_mul, map_zero, hxN, hyN, hxy]
    rcases (hdiv N).eq_zero_or_eq_zero_of_mul_eq_zero hmulN with hx0 | hy0
    · left; rw [← hxN, hx0, map_zero]
    · right; rw [← hyN, hy0, map_zero]
  have h6mem : 6 ∈ anisotropicDims FLim :=
    six_mem_anisotropicDims_of_noZeroDivisors aLim bLim cLim dLim hDLim
  have h7iso : ∀ w : Fin 7 → FLim, ∃ v : Fin 7 → FLim, v ≠ 0 ∧ ∑ r : Fin 7, w r * v r ^ 2 = 0 := by
    intro w
    obtain ⟨i, wi, hwi⟩ := hlift w
    obtain ⟨m, him, v, hv0, hvsum⟩ := hiso i wi
    refine ⟨fun r => of m (v r), ?_, ?_⟩
    · intro hvLim
      apply hv0
      funext r
      apply (of m).injective
      change of m (v r) = of m 0
      rw [map_zero]
      simpa using congr_fun hvLim r
    · have hsum : ∑ r : Fin 7, w r * (of m (v r)) ^ 2 =
          of m (∑ r : Fin 7, trans i m him (wi r) * v r ^ 2) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_mul, map_pow, ← hwi r]
        congr 1
        exact (DirectLimit.Ring.of_f (G := G) (f := trans) him (wi r)).symm
      rw [hsum, hvsum, map_zero]
  have h6ub : 6 ∈ upperBounds (anisotropicDims FLim) := by
    intro n hn
    by_contra hgt
    exact not_mem_anisotropicDims_of_ge_seven h7iso (by omega : 7 ≤ n) hn
  exact ⟨FLim, inferInstance, h2Lim, h6mem, h6ub⟩

theorem main : H1 → H2 →
    type_of% @KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture := by
  intro h1 h2 hkap
  obtain ⟨G, instF, trans, hsys, a, b, c, d, h20, hdiv, hiso⟩ := exists_tower_of_hyps h1 h2
  have h6 : IsUInvariant 6 := isUInvariant_six_of_tower G trans a b c d hdiv hiso
  obtain ⟨k, hk⟩ := hkap 6 h6
  rcases Nat.lt_or_ge k 3 with hklt | hkge
  · interval_cases k <;> omega
  · have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hkge
    omega

end OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1

end

section

open scoped TensorProduct
namespace KaplanskySeed

/-- Base change of a tensor product distributes over both factors, also for
noncommutative algebras. -/
noncomputable def tensor_basechange (K L A B : Type*) [CommRing K] [CommRing L]
    [Ring A] [Ring B] [Algebra K L] [Algebra K A] [Algebra K B] :
    L ⊗[K] (A ⊗[K] B) ≃ₐ[L] (L ⊗[K] A) ⊗[L] (L ⊗[K] B) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.distribBaseChange K L A B)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)

end KaplanskySeed

end

section

open scoped TensorProduct
open Module

namespace KaplanskySeed

/-- Scalar extension of a quaternion algebra applies the field inclusion to
each parameter and each coordinate. -/
noncomputable def quaternion_basechange (K L : Type*) [Field K] [Field L] [Algebra K L]
    (a b c : K) :
    L ⊗[K] QuaternionAlgebra K a b c ≃ₐ[L]
      QuaternionAlgebra L (algebraMap K L a) (algebraMap K L b) (algebraMap K L c) := by
  classical
  let f := algebraMap K L
  let Q := QuaternionAlgebra K a b c
  let T := QuaternionAlgebra L (f a) (f b) (f c)
  let incl : Q →ₗ[K] T :=
    { toFun := fun x => ⟨f x.re,f x.imI,f x.imJ,f x.imK⟩
      map_add' := by intro x y; ext <;> simp [Q,T]
      map_smul' := by
        intro k x
        ext <;> change f (k * _) = k • f _ <;> rw [Algebra.smul_def] <;> exact map_mul f k _ }
  have one : incl 1=1 := by ext <;> simp [incl,Q,T]
  have mul (x y : Q) : incl (x*y) = incl x*incl y := by
    rcases x with ⟨_,_,_,_⟩
    rcases y with ⟨_,_,_,_⟩
    simp [incl,Q,T,QuaternionAlgebra.mk_mul_mk]
  let extended := incl.liftBaseChange L
  have surj : Function.Surjective extended := by
    rintro ⟨x,y,z,t⟩
    refine ⟨(x ⊗ₜ[K] (⟨1,0,0,0⟩ : Q)) + (y ⊗ₜ[K] (⟨0,1,0,0⟩ : Q)) +
      (z ⊗ₜ[K] (⟨0,0,1,0⟩ : Q)) + (t ⊗ₜ[K] (⟨0,0,0,1⟩ : Q)),?_⟩
    ext <;> simp [extended,incl,Q,T]
  have dim : finrank L (L ⊗[K] Q) = finrank L T :=
    (finrank_eq_card_basis ((QuaternionAlgebra.basisOneIJK a b c).baseChange L)).trans
      (finrank_eq_card_basis (QuaternionAlgebra.basisOneIJK (f a) (f b) (f c))).symm
  let : FiniteDimensional L (L ⊗[K] Q) := Module.Finite.of_basis ((QuaternionAlgebra.basisOneIJK a b c).baseChange L)
  let e : (L ⊗[K] Q) ≃ₗ[L] T := LinearEquiv.ofBijective extended
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mpr surj,surj⟩
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct e ?_ ?_
  · intro r s x y
    change extended ((r*s) ⊗ₜ[K] (x*y)) = extended (r ⊗ₜ[K] x) * extended (s ⊗ₜ[K] y)
    simp [extended,mul,smul_smul,mul_comm r s]
  · change extended (1 ⊗ₜ[K] 1) = 1
    simp [extended,one]

end KaplanskySeed

end

section

open scoped TensorProduct

namespace KaplanskySeed

/-- Extending scalars in the biquaternion algebra commutes with extending all
four of its Hilbert symbol parameters along the field inclusion. -/
noncomputable def biquaternion_basechange (K L : Type*) [Field K] [Field L] [Algebra K L]
    (a b c d : K) :
    L ⊗[K] (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d) ≃ₐ[L]
      QuaternionAlgebra L (algebraMap K L a) 0 (algebraMap K L b) ⊗[L]
      QuaternionAlgebra L (algebraMap K L c) 0 (algebraMap K L d) := by
  let changeQ (u v : K) : L ⊗[K] QuaternionAlgebra K u 0 v ≃ₐ[L]
      QuaternionAlgebra L (algebraMap K L u) 0 (algebraMap K L v) := by
    exact cast (congrArg (fun z : L => L ⊗[K] QuaternionAlgebra K u 0 v ≃ₐ[L]
      QuaternionAlgebra L (algebraMap K L u) z (algebraMap K L v))
      (map_zero (algebraMap K L))) (quaternion_basechange K L u 0 v)
  exact (tensor_basechange K L _ _).trans (Algebra.TensorProduct.congr (changeQ a b) (changeQ c d))

end KaplanskySeed

end

section

/-!
For the diagonal characteristic-not-two case of the proof of EKM, Theorem
30.5, a right polynomial lattice is constructed from ordered Clifford
monomials. A generator for the lattice simultaneously conjugates the given
family to polynomials. Coefficient comparison then descends one variable.
-/

section

open Polynomial
namespace KaplanskyTower

/-- A nonzero additive subgroup of the polynomial ring over a division ring, closed under
right multiplication, is generated on the right by a monic polynomial. -/
theorem polynomial_right_principal {D : Type*} [DivisionRing D] (I : AddSubgroup D[X])
    (nonzero : ∃ p ∈ I, p ≠ 0) (right : ∀ p ∈ I, ∀ q : D[X], p*q ∈ I) :
    ∃ u ∈ I, u.Monic ∧ ∀ p ∈ I, ∃ q, p = u*q := by
  classical
  let property (n : ℕ) := ∃ p ∈ I, p ≠ 0 ∧ p.natDegree = n
  have inhabited : ∃ n, property n := by
    obtain ⟨p,hp,notzero⟩ := nonzero
    exact ⟨p.natDegree,p,hp,notzero,rfl⟩
  obtain ⟨p,hp,np,degr⟩ := Nat.find_spec inhabited
  let u := p * C p.leadingCoeff⁻¹
  have mon : u.Monic := monic_mul_leadingCoeff_inv np
  have inI : u ∈ I := right p hp _
  have du : u.natDegree = Nat.find inhabited := by
    dsimp [u]
    rw [natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr np)),degr]
  refine ⟨u,inI,mon,?_⟩
  intro v hv
  have sum := modByMonic_add_div v u
  have inside : v %ₘ u ∈ I := by
    have h := I.sub_mem hv (right u inI (v /ₘ u))
    rw [eq_sub_of_add_eq sum]
    exact h
  have zero : v %ₘ u = 0 := by
    by_contra ne
    have low := natDegree_lt_natDegree ne (degree_modByMonic_lt v mon)
    have high : Nat.find inhabited ≤ (v %ₘ u).natDegree :=
      Nat.find_min' inhabited ⟨v %ₘ u,inside,ne,rfl⟩
    omega
  exact ⟨v /ₘ u,by simpa [zero] using sum.symm⟩

/-- A fractional right polynomial ideal over a division ring is principal whenever it admits
a common left denominator. No centrality assumption on that denominator is needed. -/
theorem principal_fractional_lattice {D E : Type*} [DivisionRing D] [DivisionRing E]
    (j : D[X] →+* E) (inj : Function.Injective j) (L : AddSubgroup E)
    (nonzero : ∃ x ∈ L, x ≠ 0) (right : ∀ x ∈ L, ∀ p : D[X], x*j p ∈ L)
    (clear : ∃ c : E, c ≠ 0 ∧ ∀ x ∈ L, ∃ p, j p = c*x) :
    ∃ u ∈ L, u ≠ 0 ∧ ∀ x ∈ L, ∃ p : D[X], x = u*j p := by
  classical
  obtain ⟨c,hc,denom⟩ := clear
  let I : AddSubgroup D[X] :=
    { carrier := {p | c⁻¹ * j p ∈ L}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change c⁻¹ * j (x+y) ∈ L
        simpa only [map_add,mul_add] using L.add_mem hx hy
      neg_mem' := by
        intro x hx
        change c⁻¹ * j (-x) ∈ L
        simpa only [map_neg,mul_neg] using L.neg_mem hx }
  have stable (p : D[X]) (hp : p ∈ I) (q : D[X]) : p*q ∈ I := by
    change c⁻¹ * j (p*q) ∈ L
    rw [map_mul,← mul_assoc]
    exact right _ hp _
  have inhabited : ∃ p ∈ I,p ≠ 0 := by
    obtain ⟨x,hx,xne⟩ := nonzero
    obtain ⟨a,ha⟩ := denom _ hx
    refine ⟨a,?_,?_⟩
    · change c⁻¹*j a ∈ L
      rwa [ha,inv_mul_cancel_left₀ hc]
    · intro az
      rw [az,map_zero] at ha
      exact (mul_ne_zero hc xne) ha.symm
  obtain ⟨p,hp,mon,gen⟩ := polynomial_right_principal I inhabited stable
  have nonzeroP : j p ≠ 0 := fun h => mon.ne_zero (inj ((map_zero j).symm ▸ h))
  refine ⟨c⁻¹*j p,hp,mul_ne_zero (inv_ne_zero hc) nonzeroP,?_⟩
  intro x hx
  obtain ⟨v,hv⟩ := denom x hx
  have eq : c⁻¹*j v = x := by rw [hv,inv_mul_cancel_left₀ hc]
  have mem : v ∈ I := by change c⁻¹*j v ∈ L; rwa [eq]
  obtain ⟨q,hq⟩ := gen v mem
  exact ⟨q, by rw [← eq,hq,map_mul,mul_assoc]⟩

/-- A family preserving the same fractional lattice can be conjugated simultaneously
into the polynomial ring. -/
theorem simultaneous_polynomial {D E : Type*} [DivisionRing D] [DivisionRing E]
    (j : D[X] →+* E) (inj : Function.Injective j) (L : AddSubgroup E)
    (nonzero : ∃ x ∈ L, x ≠ 0) (right : ∀ x ∈ L, ∀ p : D[X], x*j p ∈ L)
    (clear : ∃ c : E, c ≠ 0 ∧ ∀ x ∈ L, ∃ p, j p = c*x)
    (Y : Set E) (stable : ∀ y ∈ Y, ∀ x ∈ L, y*x ∈ L) :
    ∃ u : E, u ≠ 0 ∧ ∀ y ∈ Y, ∃ p : D[X], j p = u⁻¹*y*u := by
  obtain ⟨u,hu,une,gen⟩ := principal_fractional_lattice j inj L nonzero right clear
  refine ⟨u,une,?_⟩
  intro y hy
  obtain ⟨p,eq⟩ := gen (y*u) (stable y hy u hu)
  exact ⟨p,by rw [mul_assoc,eq,inv_mul_cancel_left₀ une]⟩

end KaplanskyTower

end

section

namespace KaplanskyStraight

/-- Ordered products of an anticommuting family are stable, up to central
coefficients, under left multiplication by every family member. -/
theorem stable_words {R E : Type*} [CommRing R] [Ring E] [Algebra R E]
    (ys : List E) (anti : ys.Pairwise fun a b => b*a = -(a*b))
    (square : ∀ y∈ys,∃ c:R,y*y=algebraMap R E c) :
    ∃ words : List E, 1∈words ∧ ∀ y∈ys, ∀ u∈words,
      ∃ v∈words,∃ c:R,y*u=v*algebraMap R E c := by
  induction ys with
  | nil => exact ⟨[1],by simp,by simp⟩
  | cons a ys ih =>
    obtain ⟨comm,rest⟩ := List.pairwise_cons.mp anti
    obtain ⟨tail,one,stable⟩ := ih rest (fun _ h => square _ (List.mem_cons_of_mem _ h))
    let all := tail ++ tail.map (fun v => a*v)
    have old {v:E} (h:v∈tail) : v∈all := List.mem_append_left _ h
    have new {v:E} (h:v∈tail) : a*v∈all := List.mem_append_right _ (List.mem_map.mpr ⟨v,h,rfl⟩)
    refine ⟨all,old one,?_⟩
    intro y hy u hu
    have hu' := List.mem_append.mp hu
    rcases List.mem_cons.mp hy with rfl | hy
    · rcases hu' with h | h
      · exact ⟨y*u,new h,1,by simp⟩
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
        obtain ⟨c,hc⟩ := square y (List.mem_cons_self)
        exact ⟨v,old hv,c,by rw [←mul_assoc,hc,Algebra.commutes]⟩
    · rcases hu' with h | h
      · obtain ⟨v,hv,c,hc⟩ := stable y hy u h
        exact ⟨v,old hv,c,hc⟩
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
        obtain ⟨w,hw,c,hc⟩ := stable y hy v hv
        exact ⟨a*w,new hw,-c,by rw [←mul_assoc,comm y hy,neg_mul,mul_assoc,hc,←mul_assoc,map_neg,mul_neg]⟩

end KaplanskyStraight

end

section

namespace KaplanskyStraight
open Polynomial

/-- The right polynomial span of the finite Clifford monomials is a
nonzero stable lattice with a common denominator. -/
theorem stable_lattice {D E R : Type*} [DivisionRing D] [DivisionRing E] [CommRing R] [Algebra R E]
    (j : Polynomial D →+* E) (as_poly : ∀ r:R, ∃p, j p = algebraMap R E r)
    (clear : ∀ w : List E,∃c:E,c≠0 ∧ ∀v∈w,∃p,j p=c*v)
    (ys : List E) (anti : ys.Pairwise fun a b => b*a = -(a*b))
    (square : ∀ y∈ys,∃ c:R,y*y=algebraMap R E c) :
    ∃ L : AddSubgroup E, (1:E)∈L ∧
      (∀ x∈L,∀p : Polynomial D,x*j p∈L) ∧
      (∃c:E,c≠0 ∧ ∀x∈L,∃p,j p=c*x) ∧
      ∀y∈ys,∀x∈L,y*x∈L := by
  classical
  obtain ⟨words,one,stable⟩ := stable_words ys anti square
  let A : Set E := {x | ∃ v∈words, ∃ p : Polynomial D, x = v*j p}
  let L := AddSubgroup.closure A
  have term (v : E) (hv:v∈words) (p : Polynomial D) : v*j p∈L :=
    AddSubgroup.subset_closure ⟨v,hv,p,rfl⟩
  obtain ⟨c,nz,clears⟩ := clear words
  refine ⟨L,by simpa using term 1 one 1,?_,⟨c,nz,?_⟩,?_⟩
  · intro x hx p
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v,hv,q,rfl⟩ := hx
      simpa [map_mul,mul_assoc] using term v hv (q*p)
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact L.add_mem hx hy
    | neg x _ hx => rw [neg_mul]; exact L.neg_mem hx
  · intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v,hv,q,rfl⟩ := hx
      obtain ⟨p,hp⟩ := clears v hv
      exact ⟨p*q,by rw [map_mul,hp,mul_assoc]⟩
    | zero => exact ⟨0,by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨p,hp⟩ := hx
      obtain ⟨q,hq⟩ := hy
      exact ⟨p+q,by rw [map_add,hp,hq,mul_add]⟩
    | neg x _ hx =>
      obtain ⟨p,hp⟩ := hx
      exact ⟨-p,by rw [map_neg,hp,mul_neg]⟩
  · intro y hy x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v,hv,q,rfl⟩ := hx
      obtain ⟨w,hw,b,hb⟩ := stable y hy v hv
      obtain ⟨p,hp⟩ := as_poly b
      rw [←mul_assoc,hb,←hp,mul_assoc,←map_mul]
      exact term w hw _
    | zero => simp
    | add x z _ _ hx hz => rw [mul_add]; exact L.add_mem hx hz
    | neg x _ hx => rw [mul_neg]; exact L.neg_mem hx

end KaplanskyStraight

end

section

namespace KaplanskyStraight
open Polynomial

theorem constant_of_square {D : Type*} [DivisionRing D] (q : D[X]) (a : D)
    (h : q*q = C a) : q = C (q.coeff 0) := by
  by_cases q0 : q=0
  · simp [q0]
  have deg := natDegree_mul q0 q0
  rw [h,natDegree_C] at deg
  exact eq_C_of_natDegree_eq_zero (by omega)

set_option maxHeartbeats 700000 in
theorem components_of_square {D : Type*} [DivisionRing D] (p : D[X]) (u v : D)
    (h : p*p = C u * X^2+C v) :
    p.coeff 1*p.coeff 1 = u ∧ p.coeff 0*p.coeff 0 = v ∧
      p.coeff 1*p.coeff 0 = -(p.coeff 0*p.coeff 1) := by
  have le : p.natDegree ≤ 1 := by
    by_cases p0 : p=0
    · simp [p0]
    have hd := natDegree_mul p0 p0
    have bound : (C u * X^2+C v).natDegree ≤ 2 := (natDegree_add_le _ _).trans (max_le
      (natDegree_C_mul_X_pow_le u 2) (by rw [natDegree_C]; omega))
    rw [←h,hd] at bound
    omega
  have hi : p.coeff 2=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have first := congrArg (fun z : D[X] => z.coeff 0) h
  have second := congrArg (fun z : D[X] => z.coeff 1) h
  have third := congrArg (fun z : D[X] => z.coeff 2) h
  simp only [coeff_add, C_mul_X_pow_eq_monomial] at first second third
  simp [coeff_mul, Finset.Nat.antidiagonal_eq_map,Finset.sum_range_succ] at third
  change p.coeff 0*p.coeff 2 + p.coeff 1*p.coeff 1 + p.coeff 2*p.coeff 0 = u at third
  simp [hi] at third
  simp [mul_coeff_one, coeff_monomial] at second
  simp [coeff_monomial] at first
  exact ⟨third,first,eq_neg_of_add_eq_zero_left (by rwa [add_comm])⟩

end KaplanskyStraight

end

section

namespace KaplanskyStraight
open Polynomial

theorem step {D E R : Type*} [DivisionRing D] [DivisionRing E] [CommRing R] [Algebra R E]
    (j : D[X] →+* E) (inj : Function.Injective j)
    (as_poly : ∀r : R,∃p,j p=algebraMap R E r)
    (clear : ∀w : List E,∃c:E,c≠0 ∧ ∀v∈w,∃p,j p=c*v)
    {m : ℕ} (a : Fin m → D) (u v : D) (old : Fin m → E) (y : E)
    (scalar : ∀i,∃c:R,j (C (a i))=algebraMap R E c)
    (curScalar : ∃c:R,j (C u*X^2+C v)=algebraMap R E c)
    (osq : ∀i,old i*old i=j (C (a i))) (ysq : y*y=j (C u*X^2+C v))
    (anti : ∀i k,i≠k → old i*old k=-(old k*old i)) (cross : ∀i,old i*y=-(y*old i)) :
    ∃g : Fin m → D,∃b c:D, (∀i,g i*g i=a i) ∧ b*b=u ∧ c*c=v ∧ b*c=-(c*b) ∧
      (∀i k,i≠k → g i*g k=-(g k*g i)) ∧ (∀i,g i*b=-(b*g i)) ∧ (∀i,g i*c=-(c*g i)) := by
  classical
  let ys := y :: List.ofFn old
  have hanti : ys.Pairwise fun a b => b*a = -(a*b) := List.pairwise_cons.mpr ⟨by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact cross i, List.pairwise_ofFn.mpr fun {_ _} h => anti _ _ h.ne'⟩
  have hsquare (w : E) (hw : w ∈ ys) : ∃r:R,w*w=algebraMap R E r := by
    rcases List.mem_cons.mp hw with rfl | ht
    · rwa [ysq]
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
      rw [osq]; exact scalar i
  obtain ⟨L,one,closed,den,stable⟩ := stable_lattice j as_poly clear ys hanti hsquare
  obtain ⟨k,k0,hk⟩ := KaplanskyTower.simultaneous_polynomial j inj L ⟨1,one,one_ne_zero⟩ closed den {z | z∈ys} stable
  let conj (z : E) := k⁻¹*z*k
  have mul (x z : E) : conj x*conj z = conj (x*z) := by simp [conj,mul_assoc,k0]
  have neg (x : E) : conj (-x) = -conj x := by simp [conj]
  have center (p : D[X]) (hp : ∃c:R,j p=algebraMap R E c) : conj (j p)=j p := by
    obtain ⟨c,hc⟩ := hp
    rw [hc]
    change k⁻¹ * algebraMap R E c * k = _
    rw [mul_assoc,Algebra.commutes,←mul_assoc,inv_mul_cancel₀ k0,one_mul]
  obtain ⟨Y,hY⟩ := hk y (List.mem_cons_self)
  choose Q hQ using fun i => hk (old i) (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have Qsq (i : Fin m) : Q i * Q i=C (a i) := by
    apply inj
    rw [map_mul,hQ]
    exact (mul _ _).trans ((congrArg conj (osq i)).trans (center _ (scalar i)))
  have Ysq : Y*Y=C u*X^2+C v := by
    apply inj
    rw [map_mul,hY]
    exact (mul _ _).trans ((congrArg conj ysq).trans (center _ curScalar))
  let g (i : Fin m) := (Q i).coeff 0
  have Qc (i : Fin m) : Q i = C (g i) := constant_of_square _ _ (Qsq i)
  have lifted {p q : D[X]} {x z : E} (hp : j p=conj x) (hq : j q=conj z) (xz:x*z=-(z*x)) :
      p*q=-(q*p) := by
    apply inj
    rw [map_neg,map_mul,map_mul,hp,hq,mul,mul,xz,neg]
  obtain ⟨b2,c2,bc⟩ := components_of_square Y u v Ysq
  refine ⟨g,Y.coeff 1,Y.coeff 0,fun i => ?_,b2,c2,bc,?_,?_,?_⟩
  · simpa [g] using congrArg (fun p : D[X] => p.coeff 0) (Qsq i)
  · intro i l hil
    simpa [g] using congrArg (fun p : D[X] => p.coeff 0) (lifted (hQ i) (hQ l) (anti i l hil))
  · intro i
    have eqn := lifted (hQ i) hY (cross i)
    rw [Qc] at eqn
    simpa using congrArg (fun p : D[X] => p.coeff 1) eqn
  · intro i
    simpa [g] using congrArg (fun p : D[X] => p.coeff 0) (lifted (hQ i) hY (cross i))

end KaplanskyStraight

end

end

section

namespace KaplanskyIndex
open Finset

/-- Nonzero simultaneous eigenvectors with distinct eigenvalue profiles are
linearly independent. The operators need only be diagonal on the given family. -/
theorem independent_of_profiles {K A I J : Type*} [Field K] [AddCommGroup A] [Module K A]
    (v : I → A) (nz : ∀ i, v i ≠ 0) (T : J → A →ₗ[K] A) (χ : I → J → K)
    (eig : ∀ i j, T j (v i) = χ i j • v i)
    (sep : ∀ {i i'}, i ≠ i' → ∃ j, χ i j ≠ χ i' j) : LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro c zero i hi
    by_cases possible : ∃ b ∈ S, b ≠ i
    · obtain ⟨b,hb,ne⟩ := possible
      obtain ⟨j,dist⟩ := sep ne.symm
      let U : A →ₗ[K] A := T j - χ b j • LinearMap.id
      have action (a : I) : U (v a) = (χ a j - χ b j) • v a := by
        simp [U,eig,sub_smul]
      have rel := congrArg U zero
      simp only [map_sum,map_smul,action,smul_smul,map_zero] at rel
      have erased : ∑ a ∈ S.erase b, (c a * (χ a j - χ b j)) • v a = 0 := by
        rwa [← Finset.sum_erase_add _ _ hb,sub_self,mul_zero,zero_smul,add_zero] at rel
      exact (mul_eq_zero.mp (ih (S.erase b) (Finset.erase_ssubset hb) _ erased i
        (Finset.mem_erase.mpr ⟨ne.symm,hi⟩))).resolve_right (sub_ne_zero.mpr dist)
    · have single : S = {i} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hi,fun b hb => by by_contra bad; exact possible ⟨b,hb,bad⟩⟩
      rw [single,Finset.sum_singleton] at zero
      exact (smul_eq_zero.mp zero).resolve_right (nz i)

end KaplanskyIndex

namespace KaplanskyIndex

/-- Six pairwise anticommuting units give sixty-four independent Clifford monomials.
Conjugation by each generator reads one sign of a monomial's eigenvalue profile. -/
theorem sixtyfour_le_finrank_of_anticommuting {K A : Type*} [Field K] [NeZero (2 : K)]
    [Ring A] [Nontrivial A] [Algebra K A] [FiniteDimensional K A] (g : Fin 6 → Aˣ)
    (anti : ∀ i j, i ≠ j → (g i : A) * g j = -(g j * (g i : A) : A)) :
    64 ≤ Module.finrank K A := by
  classical
  let flip (k : Fin 6) (l : List (Fin 6)) := l.foldr (fun j b => if j = k then b else !b) false
  let letters (m : Fin 64) := (List.finRange 6).filter (fun j => m.val.testBit j.val)
  let word (l : List (Fin 6)) := (l.map g).prod
  have move (k : Fin 6) (l : List (Fin 6)) :
      (g k : A) * (word l : A) = if flip k l then -((word l : A) * (g k : A))
        else (word l : A) * (g k : A) := by
    induction l with
    | nil => simp [flip,word]
    | cons j l ih =>
      change (g k : A) * ((g j : A) * (word l : A)) = _
      have split : flip k (j::l) = if j = k then flip k l else !flip k l := rfl
      rw [split]
      change (g k : A) * ((g j : A) * (word l : A)) = if _ then
        -((g j : A) * (word l : A) * (g k : A)) else (g j : A) * (word l : A) * (g k : A)
      by_cases eq : j = k
      · subst j
        calc
          _ = (g k : A) * (if flip k l then -((word l : A) * (g k : A))
                  else (word l : A) * (g k : A)) := congrArg (fun z : A => (g k : A) * z) ih
          _ = _ := by cases flip k l <;> simp [mul_assoc]
      · rw [← mul_assoc,anti k j (Ne.symm eq),neg_mul,mul_assoc,ih]
        cases flip k l <;> simp [eq,mul_assoc]
  let v (m : Fin 64) : A := word (letters m)
  let T (k : Fin 6) : A →ₗ[K] A := {
    toFun := fun x => (g k : A) * x * ((g k)⁻¹ : Aˣ)
    map_add' := fun _ _ => by simp [mul_add,add_mul]
    map_smul' := fun r x => by simp [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
  }
  let χ (m : Fin 64) (k : Fin 6) : K := if flip k (letters m) then -1 else 1
  have eig (m : Fin 64) (k : Fin 6) : T k (v m) = χ m k • v m := by
    change ((g k : A) * (word _ : A)) * ((g k)⁻¹ : Aˣ) = _
    rw [move]
    cases h : flip k (letters m) <;> simp [χ,v,h,mul_assoc,neg_mul]
  let decode (f : Fin 6 → Bool) : ℕ :=
    let parity := (List.finRange 6).foldr (fun i b => Bool.xor (f i) b) false
    ((List.finRange 6).map (fun k => if Bool.xor (f k) parity then 2 ^ k.val else 0)).sum
  have inverse : ∀ m : Fin 64, decode (fun k => flip k (letters m)) = m.val := by decide
  have sep {a b : Fin 64} (ne : a ≠ b) : ∃ k, χ a k ≠ χ b k := by
    by_contra! same
    have flags : (fun k => flip k (letters a)) = (fun k => flip k (letters b)) := by
      funext k
      have eq := same k
      have diff : (-1 : K) ≠ 1 := by
        intro bad
        exact NeZero.ne (2 : K) (by linear_combination -bad)
      cases ha : flip k (letters a) <;> cases hb : flip k (letters b)
      · rfl
      · exact False.elim (diff (by simpa [χ,ha,hb] using eq.symm))
      · exact False.elim (diff (by simpa [χ,ha,hb] using eq))
      · rfl
    exact ne (Fin.ext ((inverse a).symm.trans ((congrArg decode flags).trans (inverse b))))
  have indep := independent_of_profiles v (fun m => (word (letters m)).ne_zero) T χ eig sep
  simpa using indep.fintype_card_le_finrank

end KaplanskyIndex

namespace KaplanskyIndex
open scoped TensorProduct
open Polynomial

/-- A biquaternion algebra cannot represent the six nondegenerate generators
of an even Clifford algebra in rank seven. -/
theorem no_biquaternion_clifford_generators {K : Type*} [Field K] [NeZero (2 : K)]
    (a b c d : K) (weight : Fin 6 → K) (nz : ∀ i, weight i ≠ 0) :
    ¬ ∃ x : Fin 6 → (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d),
      (∀ i, x i ^ 2 = algebraMap K _ (weight i)) ∧
      ∀ i j, i ≠ j → x i * x j = -(x j * x i) := by
  rintro ⟨x,square,anti⟩
  let D := QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d
  have ux (i : Fin 6) : IsUnit (x i) := by
    apply (isUnit_pow_iff (n := 2) (by decide)).mp
    rw [square]
    exact (isUnit_iff_ne_zero.mpr (nz i)).map (algebraMap K D)
  let g (i : Fin 6) := (ux i).unit
  have size : Module.finrank K D = 16 := by
    rw [show Module.finrank K D = _ from Module.finrank_tensorProduct,
      QuaternionAlgebra.finrank_eq_four,QuaternionAlgebra.finrank_eq_four]
  have : Nontrivial D := Module.nontrivial_of_finrank_pos (by rw [size]; decide : 0 < Module.finrank K D)
  have : FiniteDimensional K D := Module.finite_of_finrank_pos (by rw [size]; decide : 0 < Module.finrank K D)
  have dim : 64 ≤ Module.finrank K D := sixtyfour_le_finrank_of_anticommuting (K := K) g (fun i j h =>
    by simpa [g] using anti i j h)
  rw [size] at dim
  exact (by decide : ¬ 64 ≤ 4 * 4) dim

end KaplanskyIndex

namespace KaplanskyIndex
open scoped TensorProduct
open QuadraticMap CliffordAlgebra

/-- The ordinary even Clifford algebra of a nondegenerate seven-dimensional
diagonal form has no unital algebra homomorphism to a biquaternion algebra. -/
theorem no_even_clifford_to_biquaternion {K : Type*} [Field K] [NeZero (2 : K)]
    (a b c d : K) (w : Fin 7 → K) (nz : ∀ i, w i ≠ 0) :
    IsEmpty (CliffordAlgebra.even (weightedSumSquares K w) →ₐ[K]
      (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d)) := by
  classical
  let Q := weightedSumSquares K w
  let e (i j : Fin 7) : K := if j=i then 1 else 0
  let v (i : Fin 7) := CliffordAlgebra.ι Q (e i)
  have diag (i : Fin 7) : Q (e i) = w i := by
    simp [Q,e,mul_ite,Finset.sum_ite_eq']
  have orth (i j : Fin 7) (hij : i ≠ j) : Q.IsOrtho (e i) (e j) := by
    change Q (e i + e j) = Q (e i) + Q (e j)
    simp only [Q,weightedSumSquares_apply,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : k=i
    · subst k
      simp [e,hij]
    · simp [e,h]
  have square (i : Fin 7) : v i * v i = algebraMap K _ (w i) := by
    change ι Q _ * ι Q _ = _
    rw [ι_sq_scalar,diag]
  have antic (i j : Fin 7) (hij : i ≠ j) : v i * v j = -(v j * v i) :=
    ι_mul_ι_comm_of_isOrtho (orth i j hij)
  let z (i : Fin 6) : CliffordAlgebra.even Q := (even.ι Q).bilin (e i.succ) (e 0)
  have zv (i : Fin 6) : (z i : CliffordAlgebra Q) = v i.succ * v 0 := rfl
  have pair (i j : Fin 6) :
      (z i : CliffordAlgebra Q) * (z j : CliffordAlgebra Q) =
        -((v i.succ * v j.succ) * algebraMap K _ (w 0)) := by
    rw [zv,zv]
    calc
      _ = (v i.succ * (v 0 * v j.succ)) * v 0 := by noncomm_ring
      _ = _ := by rw [antic 0 j.succ (Fin.succ_ne_zero _).symm,← square]; noncomm_ring
  let weight (i : Fin 6) := -(w i.succ * w 0)
  have zs (i : Fin 6) : z i ^ 2 = algebraMap K _ (weight i) := by
    rw [pow_two]
    apply Subtype.ext
    change (z i : CliffordAlgebra Q) * (z i : CliffordAlgebra Q) = algebraMap K _ (weight i)
    rw [pair,square]
    simp [weight]
  have za (i j : Fin 6) (hij : i ≠ j) : z i * z j = -(z j * z i) := by
    apply Subtype.ext
    change (z i : CliffordAlgebra Q) * (z j : CliffordAlgebra Q) =
        -((z j : CliffordAlgebra Q) * (z i : CliffordAlgebra Q))
    rw [pair,pair,antic i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))]
    simp
  refine ⟨fun f => no_biquaternion_clifford_generators a b c d weight
    (fun i => neg_ne_zero.mpr (mul_ne_zero (nz i.succ) (nz 0))) ?_⟩
  exact ⟨fun i => f (z i),fun i => by rw [← map_pow,zs,AlgHom.commutes],
    fun i j hij => by rw [← map_mul,za i j hij,map_neg,map_mul]⟩

end KaplanskyIndex

end

section

/-! A rational-parameter pencil extracts a Clifford frame from any square root on the affine chart, by iterating the one-variable straightening argument in EKM, Theorem 30.5. -/

section

namespace KaplanskyTrans
open Polynomial
open scoped TensorProduct

/-- Purely transcendental extension preserves the absence of zero divisors,
including for noncommutative coefficient algebras. -/
theorem ratFunc_noZeroDivisors (K A : Type*) [Field K] [Ring A] [Algebra K A]
    [NoZeroDivisors A] : NoZeroDivisors (RatFunc K ⊗[K] A) := by
  classical
  let j : K[X] →ₐ[K] RatFunc K := IsScalarTower.toAlgHom K K[X] (RatFunc K)
  let f : K[X] ⊗[K] A →ₐ[K] RatFunc K ⊗[K] A := Algebra.TensorProduct.map j (AlgHom.id K A)
  have hf : Function.Injective f := by
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := A) j.toLinearMap
      (RatFunc.algebraMap_injective K)
  let eqv := (Algebra.TensorProduct.comm K K[X] A).trans (polyEquivTensor K A).symm
  let _ : NoZeroDivisors (K[X] ⊗[K] A) :=
    Function.Injective.noZeroDivisors eqv eqv.injective (map_zero _) (map_mul _)
  have scal (p : K[X]) (a : K[X] ⊗[K] A) : f (p • a) = j p • f a := by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul q d =>
      simp only [TensorProduct.smul_tmul', smul_eq_mul, f, Algebra.TensorProduct.map_tmul,
        map_mul, AlgHom.id_apply]
    | add _ _ ih ih' => rw [smul_add, map_add, ih, ih', map_add, smul_add]
  have clear (a : RatFunc K ⊗[K] A) : ∃ (p : K[X]) (b : K[X] ⊗[K] A),
      p ≠ 0 ∧ f b = j p • a := by
    induction a using TensorProduct.induction_on with
    | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
    | tmul r d =>
      refine ⟨r.denom, r.num ⊗ₜ[K] d, r.denom_ne_zero, ?_⟩
      have den : j r.denom * r = j r.num := by
        have nz : j r.denom ≠ 0 := RatFunc.algebraMap_ne_zero r.denom_ne_zero
        exact (mul_comm _ _).trans ((eq_div_iff nz).mp (RatFunc.num_div_denom r).symm)
      rw [TensorProduct.smul_tmul', smul_eq_mul, den]
      rfl
    | add a b ha hb =>
      obtain ⟨p,u,hp,hu⟩ := ha
      obtain ⟨q,v,hq,hv⟩ := hb
      refine ⟨p*q, q • u + p • v, mul_ne_zero hp hq, ?_⟩
      rw [map_add, scal, scal, hu,hv, smul_smul, smul_smul, mul_comm (j q), map_mul, smul_add]
  constructor
  intro x y xy
  obtain ⟨p,u,hp,hu⟩ := clear x
  obtain ⟨q,v,hq,hv⟩ := clear y
  have uv : u*v=0 := hf (by
    rw [map_mul,hu,hv,map_zero, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,xy,smul_zero,smul_zero])
  rcases eq_zero_or_eq_zero_of_mul_eq_zero uv with h | h
  · exact Or.inl ((smul_eq_zero.mp (hu.symm.trans (h ▸ map_zero f))).resolve_left
      (RatFunc.algebraMap_ne_zero hp))
  · exact Or.inr ((smul_eq_zero.mp (hv.symm.trans (h ▸ map_zero f))).resolve_left
      (RatFunc.algebraMap_ne_zero hq))

end KaplanskyTrans

end

section

namespace KaplanskyTrans
open Polynomial
open scoped TensorProduct

variable (K A : Type*) [Field K] [Ring A] [Algebra K A]

/-- The coefficientwise embedding of an algebra polynomial ring into its
scalar extension by the rational function field. -/
noncomputable def polynomialImage : A[X] →ₐ[K] RatFunc K ⊗[K] A :=
  let s := IsScalarTower.toAlgHom K K[X] (RatFunc K)
  let f := Algebra.TensorProduct.map s (AlgHom.id K A)
  let e := (polyEquivTensor K A).trans (Algebra.TensorProduct.comm K A K[X])
  f.comp e.toAlgHom

theorem polynomialImage_injective : Function.Injective (polynomialImage K A) := by
  let s := IsScalarTower.toAlgHom K K[X] (RatFunc K)
  let f := Algebra.TensorProduct.map s (AlgHom.id K A)
  let e := (polyEquivTensor K A).trans (Algebra.TensorProduct.comm K A K[X])
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := A) s.toLinearMap (RatFunc.algebraMap_injective K)
  exact hf.comp e.injective

theorem polynomialImage_C (a : A) : polynomialImage K A (C a) = (1 : RatFunc K) ⊗ₜ[K] a := by
  simp [polynomialImage,Algebra.TensorProduct.includeLeft_apply]

theorem polynomialImage_map (p : K[X]) : polynomialImage K A (p.map (algebraMap K A)) =
    (algebraMap K[X] (RatFunc K) p) ⊗ₜ[K] (1:A) := by
  have h : polyEquivTensor K A (p.map (algebraMap K A)) = (1:A) ⊗ₜ[K] p := by
    apply (polyEquivTensor K A).symm.injective
    rw [AlgEquiv.symm_apply_apply,polyEquivTensor_symm_apply_tmul_eq_smul,one_smul]
  simp [polynomialImage, h]

theorem polynomialImage_X : polynomialImage K A X = RatFunc.X ⊗ₜ[K] (1:A) := by
  simpa using polynomialImage_map K A X

theorem polynomialImage_quadratic (a b : A) :
    polynomialImage K A (C a*X^2+C b) =
      ((1:RatFunc K) ⊗ₜ[K] a) * (RatFunc.X ⊗ₜ[K] (1:A))^2 + (1:RatFunc K) ⊗ₜ[K] b := by
  rw [map_add,map_mul,map_pow, polynomialImage_C, polynomialImage_C, polynomialImage_X]

/-- A finite list of rational scalar extensions admits one nonzero scalar polynomial
whose product with every member belongs to the polynomial algebra. -/
theorem polynomialImage_clear (xs : List (RatFunc K ⊗[K] A)) :
    ∃ p : K[X], p ≠ 0 ∧ ∀ x ∈ xs, ∃ q : A[X], polynomialImage K A q =
      algebraMap (RatFunc K) _ (algebraMap K[X] (RatFunc K) p) * x := by
  let s := IsScalarTower.toAlgHom K K[X] (RatFunc K)
  let j := polynomialImage K A
  have mult (p : K[X]) (u : A[X]) :
      j (p.map (algebraMap K A)*u) = s p • j u := by
    rw [map_mul, Algebra.smul_def]
    exact congrArg (· * j u) (polynomialImage_map K A p)
  have clear (a : RatFunc K ⊗[K] A) : ∃ (p : K[X]) (b : A[X]), p ≠ 0 ∧ j b = s p • a := by
    induction a using TensorProduct.induction_on with
    | zero => exact ⟨1,0,one_ne_zero,by simp⟩
    | tmul r d =>
      refine ⟨r.denom,r.num.map (algebraMap K A) * C d,r.denom_ne_zero,?_⟩
      have den : s r.denom * r = s r.num := by
        have nz : s r.denom ≠ 0 := RatFunc.algebraMap_ne_zero r.denom_ne_zero
        exact (mul_comm _ _).trans ((eq_div_iff nz).mp (RatFunc.num_div_denom r).symm)
      rw [mult, show j (C d) = _ from polynomialImage_C K A d, TensorProduct.smul_tmul',
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one,den]
    | add a b ha hb =>
      obtain ⟨p,u,hp,hu⟩ := ha
      obtain ⟨q,v,hq,hv⟩ := hb
      refine ⟨p*q, q.map (algebraMap K A)*u + p.map (algebraMap K A)*v,mul_ne_zero hp hq,?_⟩
      rw [map_add,mult,mult,hu,hv,smul_smul,smul_smul,mul_comm (s q),map_mul,smul_add]
  suffices ∃ p : K[X], p ≠ 0 ∧ ∀ x ∈ xs, ∃ q : A[X], j q = s p • x by
    obtain ⟨p,hp,h⟩ := this
    refine ⟨p,hp,?_⟩
    intro x hx
    obtain ⟨q,hq⟩ := h x hx
    refine ⟨q,?_⟩
    rw [show polynomialImage K A q = s p • x from hq,Algebra.smul_def]
    rfl
  induction xs with
  | nil => exact ⟨1,one_ne_zero,by simp⟩
  | cons x xs ih =>
    obtain ⟨p,u,hp,hu⟩ := clear x
    obtain ⟨q,hq,htail⟩ := ih
    refine ⟨p*q, mul_ne_zero hp hq,?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨q.map (algebraMap K A)*u,by rw [mult,hu,smul_smul,mul_comm (s q),map_mul]⟩
    · obtain ⟨v,hv⟩ := htail y hy
      exact ⟨p.map (algebraMap K A)*v,by rw [mult,hv,smul_smul,map_mul]⟩


/-- The same common denominator as a central nonzero element of the tensor algebra. -/
theorem polynomialImage_clear_central [Nontrivial A] (xs : List (RatFunc K ⊗[K] A)) :
    ∃ z : RatFunc K ⊗[K] A, z ≠ 0 ∧ (∀ x, Commute z x) ∧
      (∀ x ∈ xs, ∃ q : A[X], polynomialImage K A q = z*x) ∧
      ∃ p : K[X], polynomialImage K A (p.map (algebraMap K A)) = z := by
  obtain ⟨p,hp,h⟩ := polynomialImage_clear K A xs
  let z := algebraMap (RatFunc K) (RatFunc K ⊗[K] A) (algebraMap K[X] (RatFunc K) p)
  have eq : polynomialImage K A (p.map (algebraMap K A)) = z := polynomialImage_map K A p
  have nz : z ≠ 0 := by
    intro hz
    have zeroP := polynomialImage_injective K A (eq.trans (hz.trans (map_zero _).symm))
    apply hp
    exact Polynomial.map_injective (algebraMap K A) (algebraMap K A).injective
      (zeroP.trans (Polynomial.map_zero _).symm)
  exact ⟨z,nz,Algebra.commutes _,h,p,eq⟩

end KaplanskyTrans

end

section

open scoped TensorProduct
open Polynomial
namespace KaplanskyStraight

/-- Over a rational-function extension of a finite division algebra, an anticommuting
family with one quadratic square specializes to a family with two more constant terms. -/
theorem ratFunc_step {K D : Type*} [Field K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] {m : ℕ} (c : Fin m → K) (b a : K)
    (old : Fin m → RatFunc K ⊗[K] D) (y : RatFunc K ⊗[K] D)
    (osq : ∀ i, old i*old i = algebraMap (RatFunc K) _ (RatFunc.C (c i)))
    (ysq : y*y = algebraMap (RatFunc K) _ (RatFunc.C b*RatFunc.X^2+RatFunc.C a))
    (anti : ∀ i k, i ≠ k → old i*old k = -(old k*old i))
    (cross : ∀ i, old i*y = -(y*old i)) :
    ∃ g : Fin m → D, ∃ v w : D,
      (∀ i, g i*g i=algebraMap K D (c i)) ∧ v*v=algebraMap K D b ∧ w*w=algebraMap K D a ∧
      v*w=-(w*v) ∧ (∀ i k, i ≠ k → g i*g k=-(g k*g i)) ∧
      (∀ i, g i*v=-(v*g i)) ∧ (∀ i, g i*w=-(w*g i)) := by
  let E := RatFunc K ⊗[K] D
  let j := (KaplanskyTrans.polynomialImage K D).toRingHom
  let f := (algebraMap (RatFunc K) E).comp (algebraMap K[X] (RatFunc K))
  let : Algebra K[X] E := f.toAlgebra' (fun p z => Algebra.commutes _ _)
  have central (p : K[X]) : j (p.map (algebraMap K D)) = algebraMap K[X] E p :=
    KaplanskyTrans.polynomialImage_map K D p
  have i1 (k : K) : j (C (algebraMap K D k)) = algebraMap (RatFunc K) E (RatFunc.C k) := by
    have h := central (C k)
    simpa [f, RingHom.algebraMap_toAlgebra', RatFunc.algebraMap_C] using h
  have i2 : j (C (algebraMap K D b)*X^2+C (algebraMap K D a)) =
      algebraMap (RatFunc K) E (RatFunc.C b*RatFunc.X^2+RatFunc.C a) := by
    have h := central (C b*X^2+C a)
    simpa [f, RingHom.algebraMap_toAlgebra', RatFunc.algebraMap_C, RatFunc.algebraMap_X] using h
  have one_ne : (1:E) ≠ 0 := fun h => one_ne_zero
    (KaplanskyTrans.polynomialImage_injective K D (((map_one j).trans h).trans (map_zero j).symm))
  let : Nontrivial E := nontrivial_of_ne 1 0 one_ne
  let : NoZeroDivisors E := KaplanskyTrans.ratFunc_noZeroDivisors K D
  let : IsDomain E := NoZeroDivisors.to_isDomain E
  let : DivisionRing E := divisionRingOfFiniteDimensional (RatFunc K) E
  apply step (R := K[X]) j (KaplanskyTrans.polynomialImage_injective K D)
    (fun p => ⟨_,central p⟩) ?_ (fun i => algebraMap K D (c i))
    (algebraMap K D b) (algebraMap K D a) old y ?_ ?_ ?_ ?_ anti cross
  · intro words
    obtain ⟨z,nz,hc,mem,p,hp⟩ := KaplanskyTrans.polynomialImage_clear_central K D words
    exact ⟨z,nz,mem⟩
  · intro i
    exact ⟨C (c i), by simpa using central (C (c i))⟩
  · refine ⟨C b*X^2+C a,?_⟩
    rw [i2]
    change _ = algebraMap (RatFunc K) E (algebraMap K[X] (RatFunc K) _)
    simp [RatFunc.algebraMap_C,RatFunc.algebraMap_X]
  · intro i
    exact (osq i).trans (i1 _).symm
  · exact ysq.trans i2.symm

end KaplanskyStraight

end

section

open scoped TensorProduct
open Polynomial

namespace KaplanskyTrans

universe u

/-- A list of square roots with the Clifford anticommutation relations. -/
abbrev Frame {K A : Type u} [Field K] [Ring A] [Algebra K A] {n : ℕ} (c : Fin n → K) :=
  ∃ g : Fin n → A, (∀ i, g i*g i = algebraMap K A (c i)) ∧
    ∀ i j, i ≠ j → g i*g j = -(g j*g i)

theorem noncomm_basechange (K S T A : Type u) [Field K] [Field S] [Field T]
    [Ring A] [Algebra K A] [Algebra K S] [Algebra K T] [Algebra S T] [IsScalarTower K S T] :
    Nonempty ((T ⊗[K] A) ≃ₐ[T] T ⊗[S] (S ⊗[K] A)) :=
  ⟨AlgEquiv.ofLinearEquiv
    (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange K S T T A).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul fun _ _ _ _ => by simp)⟩

/-- Unfold the variables of a diagonal affine pencil, preserving the
algebra and recovering a whole Clifford frame from one square root. -/
theorem pencil_induction
    (step : ∀ (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A]
        [FiniteDimensional K A] [NoZeroDivisors A] {n : ℕ} (a b : K) (c : Fin n → K),
      Frame (A := RatFunc K ⊗[K] A)
        (Fin.cons (algebraMap K (RatFunc K) b * RatFunc.X^2 + algebraMap K (RatFunc K) a)
          (fun i => algebraMap K (RatFunc K) (c i))) →
      Frame (A := A) (Fin.cons a (Fin.cons b c))) (n : ℕ) (K A : Type u)
    [Field K] [Ring A] [Nontrivial A] [Algebra K A] [FiniteDimensional K A] [NoZeroDivisors A]
    (a : K) (c : Fin n → K) :
    ∃ (T : Type u) (_ : Field T) (_ : Algebra K T) (t : Fin n → T) (δ : T),
      NoZeroDivisors (T ⊗[K] A) ∧
      δ = algebraMap K T a + ∑ i, algebraMap K T (c i) * t i ^ 2 ∧
      (∀ x : T ⊗[K] A, x*x = algebraMap T _ δ → Frame (A := A) (Fin.cons a c)) := by
  induction n generalizing K A with
  | zero =>
    let e := Algebra.TensorProduct.lid K A
    refine ⟨K, inferInstance, inferInstance, Fin.elim0, a,
      Function.Injective.noZeroDivisors e e.injective (map_zero _) (map_mul _), by simp, ?_⟩
    intro x hx
    refine ⟨fun _ => e x, ?_, ?_⟩
    · intro i
      have hi : i=0 := Fin.ext (by omega)
      subst i
      change e x * e x = algebraMap K A a
      rw [←map_mul, hx,e.commutes]
    · intro i j ne
      exact (ne (Fin.ext (by omega))).elim
  | succ n ih =>
    let S := RatFunc K
    let B := S ⊗[K] A
    let k := algebraMap K S
    let a' : S := k (c 0) * RatFunc.X ^ 2 + k a
    let c' (i : Fin n) := k (c i.succ)
    let _ : NoZeroDivisors B := ratFunc_noZeroDivisors K A
    let _ : Nontrivial B := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right
      K S A k.injective
    obtain ⟨T, fT, algS, ts, δ, hd, value, lift⟩ := ih S B a' c'
    let j := algebraMap S T
    let _ : Algebra K T := (j.comp k).toAlgebra
    let _ : IsScalarTower K S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨e⟩ := noncomm_basechange K S T A
    let _ := hd
    refine ⟨T, fT, inferInstance, Fin.cons (j RatFunc.X) ts, δ,
      Function.Injective.noZeroDivisors e e.injective (map_zero _) (map_mul _), ?_, ?_⟩
    · rw [value, Fin.sum_univ_succ]
      simp only [a', c', map_add, map_mul, map_pow, Fin.cons_zero, Fin.cons_succ]
      change j (k (c 0))*j RatFunc.X^2 + j (k a) + _ = j (k a) + (j (k (c 0))*j RatFunc.X^2 + _)
      ac_rfl
    · intro x hx
      have found := lift (e x) (by rw [←map_mul,hx,e.commutes])
      have descent := step K A a (c 0) (fun i => c i.succ) found
      have tu : Fin.cons (c 0) (fun i => c i.succ) = c := Fin.cons_self_tail c
      rwa [tu] at descent

end KaplanskyTrans

end

section

namespace KaplanskyTrans

theorem anticommuting_cons {A : Type*} [Ring A] {n : ℕ} (a : A) (v : Fin n → A)
    (old : ∀ i j, i ≠ j → v i * v j = -(v j * v i))
    (cross : ∀ i, v i * a = -(a * v i)) :
    let g : Fin (n+1) → A := Fin.cons a v
    ∀ i j, i ≠ j → g i * g j = -(g j * g i) := by
  intro g i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · intro h
    exact False.elim (h rfl)
  · intro _
    exact (neg_neg _).symm.trans (congrArg Neg.neg (cross j)).symm
  · intro _
    exact cross i
  · intro h
    exact old i j fun eq => h (congrArg Fin.succ eq)

universe u

theorem frame_of_parts {K A : Type u} [Field K] [Ring A] [Algebra K A] {n : ℕ}
    (a b : K) (r : Fin n → K) (g : Fin n → A) (v u : A)
    (old : ∀ i, g i*g i=algebraMap K A (r i)) (sqv : v*v=algebraMap K A b)
    (squ : u*u=algebraMap K A a) (pair : v*u=-(u*v))
    (anti : ∀ i j, i ≠ j → g i*g j=-(g j*g i))
    (yv : ∀ i, g i*v=-(v*g i)) (yu : ∀ i, g i*u=-(u*g i)) :
    Frame (A := A) (Fin.cons a (Fin.cons b r)) := by
  let h : Fin (n+1) → A := Fin.cons v g
  refine ⟨Fin.cons u h, ?_, anticommuting_cons u h (anticommuting_cons v g anti yv) ?_⟩
  · exact Fin.cases squ (Fin.cases sqv old)
  · exact Fin.cases pair yu

end KaplanskyTrans

end

section

open scoped TensorProduct
namespace KaplanskyTrans
universe u

/-- Integrate a six-generator obstruction and successive univariate pencil
straightenings into the affine equation of the original seven-dimensional form. -/
theorem rank_seven_radicand
    (step : ∀ (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A]
        [FiniteDimensional K A] [NoZeroDivisors A] {n : ℕ} (a b : K) (c : Fin n → K),
      Frame (A := RatFunc K ⊗[K] A)
        (Fin.cons (algebraMap K (RatFunc K) b * RatFunc.X^2 + algebraMap K (RatFunc K) a)
          (fun i => algebraMap K (RatFunc K) (c i))) →
      Frame (A := A) (Fin.cons a (Fin.cons b c)))
    (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A]
    [FiniteDimensional K A] [NoZeroDivisors A]
    (w : Fin 7 → K) (nw : ∀ i, w i ≠ 0)
    (obstruction : ∀ (v : Fin 6 → K), (∀ i, v i ≠ 0) →
      ¬ ∃ g : Fin 6 → A, (∀ i, (g i)^2 = algebraMap K A (v i)) ∧
        ∀ i j, i ≠ j → g i * g j = -(g j * g i)) :
    ∃ (T : Type u) (_ : Field T) (_ : Algebra K T) (tail : Fin 6 → T) (δ : T),
      NoZeroDivisors (T ⊗[K] A) ∧
      algebraMap K T (w 0) * δ + ∑ i, algebraMap K T (w i.succ) * tail i^2 = 0 ∧
      ∀ x : T ⊗[K] A, x*x ≠ algebraMap T _ δ := by
  let v (i : Fin 6) : K := -(w i.succ / w 0)
  have vanish i : w 0*v i= -w i.succ := by
    simp only [v, mul_neg]
    rw [mul_comm, div_mul_cancel₀ _ (nw 0)]
  obtain ⟨T, fT, al, ts, δ, hd, val, extract⟩ :=
    pencil_induction step 5 K A (v 0) (fun j => v j.succ)
  let f := algebraMap K T
  refine ⟨T,fT,al,Fin.cons 1 ts,δ,hd,?_,?_⟩
  · change f (w 0) * δ + ∑ i, f (w i.succ) * (Fin.cons (α := fun _ => T) 1 ts i)^2 = 0
    have vm (i : Fin 6) : f (w 0) * f (v i) = -f (w i.succ) := by
      rw [←map_mul, vanish, map_neg]
    rw [Fin.sum_univ_succ, Fin.cons_zero, val]
    simp only [Fin.cons_succ, one_pow,mul_one]
    change f (w 0) * (f (v 0) + ∑ i, f (v i.succ) * ts i ^ 2) + _ = 0
    rw [mul_add, Finset.mul_sum, vm]
    simp_rw [←mul_assoc, vm, neg_mul]
    rw [Finset.sum_neg_distrib]
    ring
  · intro x hx
    obtain ⟨g, sqr, anti⟩ := extract x hx
    apply obstruction v (fun i => neg_ne_zero.mpr (div_ne_zero (nw i.succ) (nw 0)))
    refine ⟨g, ?_, anti⟩
    intro i
    have tu : Fin.cons (v 0) (fun j => v j.succ) = v := Fin.cons_self_tail v
    simpa only [sq,tu] using sqr i

end KaplanskyTrans

end

section

namespace KaplanskyTrans
open scoped TensorProduct
universe u

theorem frame_step (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A]
    [FiniteDimensional K A] [NoZeroDivisors A] {n : ℕ} (a b : K) (c : Fin n → K) :
    Frame (A := RatFunc K ⊗[K] A)
      (Fin.cons (algebraMap K (RatFunc K) b * RatFunc.X^2 + algebraMap K (RatFunc K) a)
        (fun i => algebraMap K (RatFunc K) (c i))) →
    Frame (A := A) (Fin.cons a (Fin.cons b c)) := by
  rintro ⟨g, sqs, anti⟩
  let _ := NoZeroDivisors.to_isDomain A
  let _ := divisionRingOfFiniteDimensional K A
  obtain ⟨h, v, u, hh, hv, hu, pair, ha, hy, hz⟩ := KaplanskyStraight.ratFunc_step
    c b a (fun i => g i.succ) (g 0)
    (fun i => sqs i.succ) (sqs 0)
    (fun i j ne => anti i.succ j.succ (fun h => ne (Fin.succ_injective n h)))
    (fun i => anti i.succ 0 i.succ_ne_zero)
  exact frame_of_parts a b c h v u hh hv hu pair ha hy hz

/-- For a seven-variable nondegenerate diagonal form, the affine chart's
radicand is a nonsquare in the scalar-extended algebra whenever that
algebra cannot contain six anticommuting roots of nonzero squares. -/
theorem nonsquare_chart (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A]
    [FiniteDimensional K A] [NoZeroDivisors A] (w : Fin 7 → K) (nw : ∀ i, w i ≠ 0)
    (obstruction : ∀ (v : Fin 6 → K), (∀ i, v i ≠ 0) →
      ¬ ∃ g : Fin 6 → A, (∀ i, (g i)^2 = algebraMap K A (v i)) ∧
        ∀ i j, i ≠ j → g i * g j = -(g j * g i)) :
    ∃ (T : Type u) (_ : Field T) (_ : Algebra K T) (tail : Fin 6 → T) (δ : T),
      NoZeroDivisors (T ⊗[K] A) ∧
      algebraMap K T (w 0)*δ + ∑ i, algebraMap K T (w i.succ)*tail i^2 = 0 ∧
      ∀ x : T ⊗[K] A, x*x ≠ δ ⊗ₜ[K] (1 : A) :=
  rank_seven_radicand (@frame_step) K A w nw obstruction

end KaplanskyTrans

end

section

namespace KaplanskyTrans
open scoped TensorProduct

theorem biquaternion_chart (K : Type) [Field K] [NeZero (2 : K)] (a b c d : K) :
    let D : Type := QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d
    NoZeroDivisors D → ∀ w : Fin 7 → K, (∀ i, w i ≠ 0) →
      ∃ (T : Type) (_ : Field T) (_ : Algebra K T) (tail : Fin 6 → T) (δ : T),
        NoZeroDivisors (T ⊗[K] D) ∧
        algebraMap K T (w 0) * δ + ∑ i, algebraMap K T (w i.succ) * tail i ^ 2 = 0 ∧
        ∀ x : T ⊗[K] D, x*x ≠ δ ⊗ₜ[K] (1 : D) := by
  intro D hD w hw
  let _ := hD
  have size : Module.finrank K D = 16 := by
    rw [show Module.finrank K D = _ from Module.finrank_tensorProduct,
      QuaternionAlgebra.finrank_eq_four, QuaternionAlgebra.finrank_eq_four]
  let _ : Nontrivial D := Module.nontrivial_of_finrank_pos (by rw [size]; decide : 0 < Module.finrank K D)
  let _ : FiniteDimensional K D := Module.finite_of_finrank_pos (by rw [size]; decide : 0 < Module.finrank K D)
  exact nonsquare_chart K D w hw (KaplanskyIndex.no_biquaternion_clifford_generators a b c d)

end KaplanskyTrans

end

end

section

namespace KaplanskyQuadric

/-- Over a division ring, a central quadratic extension has no zero divisors
exactly when its radicand has no square root in the division ring. This
coordinate calculation uses the coefficient order arising from a central
indeterminate and does not require the division ring to commute. -/
theorem quadratic_pair_criterion {D : Type*} [DivisionRing D] (δ : D) :
    (∀ a b c d : D, a * c + b * δ * d = 0 → a * d + b * c = 0 →
      (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0)) ↔ (∀ u : D, u * u ≠ δ) := by
  constructor
  · intro nozero u square
    have first : -u * u + 1 * δ * 1 = 0 := by simp [square]
    have second : -u * 1 + 1 * u = 0 := by simp
    rcases nozero (-u) 1 u 1 first second with zero | zero <;> exact one_ne_zero zero.2
  · intro nosquare a b c d hre him
    by_cases hb : b = 0
    · subst b
      by_cases ha : a = 0
      · exact Or.inl ⟨ha, rfl⟩
      · right
        exact ⟨(mul_eq_zero.mp (by simpa using hre)).resolve_left ha,
          (mul_eq_zero.mp (by simpa using him)).resolve_left ha⟩
    let u := b⁻¹ * a
    have bu : b * u = a := by simp [u, hb]
    have real : u * c + δ * d = 0 := by
      apply (mul_eq_zero.mp (show b * (u * c + δ * d) = 0 by
        simpa only [mul_add, ← mul_assoc, bu] using hre)).resolve_left hb
    have imag : u * d + c = 0 := by
      apply (mul_eq_zero.mp (show b * (u * d + c) = 0 by
        simpa only [mul_add, ← mul_assoc, bu] using him)).resolve_left hb
    have ceq : c = -(u * d) := (eq_neg_of_add_eq_zero_left (by simpa [add_comm] using imag))
    have cancel : (δ - u * u) * d = 0 := by
      rw [ceq, mul_neg, ← mul_assoc] at real
      rw [sub_mul, sub_eq_neg_add]
      exact real
    have dz : d = 0 := (mul_eq_zero.mp cancel).resolve_left
      (sub_ne_zero.mpr (nosquare u).symm)
    exact Or.inr ⟨by simpa [dz] using ceq, dz⟩

end KaplanskyQuadric

end

section

namespace KaplanskyQuadric
open scoped TensorProduct

/-- Scalar extension to a quadratic algebra preserves division precisely
when the radicand has no square root in the original division algebra. -/
theorem nosquare_iff_quadratic_tensor {K D : Type*} [Field K] [DivisionRing D] [Algebra K D]
    (δ : K) :
    NoZeroDivisors (QuadraticAlgebra K δ 0 ⊗[K] D) ↔
      ∀ u : D, u * u ≠ algebraMap K D δ := by
  let Q := QuadraticAlgebra K δ 0
  let w : Q := QuadraticAlgebra.omega
  let pair (a b : D) : Q ⊗[K] D := (1 : Q) ⊗ₜ[K] a + w ⊗ₜ[K] b
  let re : Q ⊗[K] D →ₗ[K] D :=
    (TensorProduct.lid K D).toLinearMap.comp ((QuadraticAlgebra.reₗ δ 0).rTensor D)
  let im : Q ⊗[K] D →ₗ[K] D :=
    (TensorProduct.lid K D).toLinearMap.comp ((QuadraticAlgebra.imₗ δ 0).rTensor D)
  have parts (a b : D) : re (pair a b) = a ∧ im (pair a b) = b := by
    have re1 : (1 : Q).re = 1 := rfl
    have im1 : (1 : Q).im = 0 := rfl
    simp [pair, re, im, w, re1, im1]
  have zero (a b : D) : pair a b = 0 ↔ a = 0 ∧ b = 0 := by
    constructor
    · intro h
      exact ⟨(parts a b).1.symm.trans ((congrArg re h).trans (map_zero re)),
        (parts a b).2.symm.trans ((congrArg im h).trans (map_zero im))⟩
    · rintro ⟨rfl, rfl⟩
      simp [pair]
  have decompose (x : Q ⊗[K] D) : ∃ a b, x = pair a b := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, ((zero 0 0).2 ⟨rfl, rfl⟩).symm⟩
    | tmul v d =>
      obtain ⟨r, s⟩ := v
      refine ⟨r • d, s • d, ?_⟩
      rw [QuadraticAlgebra.mk_eq_add_smul_omega, TensorProduct.add_tmul]
      simp [pair, w, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    | add x y hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      exact ⟨a + c, b + d, by simp only [pair, TensorProduct.tmul_add]; abel⟩
  have product (a b c d : D) :
      pair a b * pair c d = pair (a*c+b*algebraMap K D δ*d) (a*d+b*c) := by
    have ww : w*w = δ • (1 : Q) := by simp [w, Q, QuadraticAlgebra.omega_mul_omega_eq_add]
    have scalar : b * algebraMap K D δ * d = δ • (b*d) := by
      rw [← Algebra.commutes δ b, ← Algebra.smul_def, smul_mul_assoc]
    simp only [pair, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      ww, scalar, TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    abel
  rw [← quadratic_pair_criterion]
  constructor
  · intro domain a b c d hre him
    have z : pair a b * pair c d = 0 := (product a b c d).trans ((zero _ _).2 ⟨hre,him⟩)
    exact (domain.eq_zero_or_eq_zero_of_mul_eq_zero z).imp (zero a b).mp (zero c d).mp
  · intro criterion
    constructor
    intro x y h
    obtain ⟨a, b, rfl⟩ := decompose x
    obtain ⟨c, d, rfl⟩ := decompose y
    obtain ⟨hre, him⟩ := (zero _ _).mp ((product a b c d).symm.trans h)
    exact (criterion a b c d hre him).imp (zero a b).mpr (zero c d).mpr

end KaplanskyQuadric

end

section

namespace KaplanskyQuadric
open scoped TensorProduct
universe u v

/-- An affine chart of a diagonal quadric. A nonsquare radicand in the division algebra
gives a field over which the form has a nonzero isotropic vector and the scalar-extended
algebra continues to have no zero divisors. The tail may be specialized to independent
indeterminates, with its last coordinate set equal to one. -/
theorem split_diagonal_of_no_square {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
    {n : ℕ} (w : Fin (n+1) → K) (tail : Fin n → K)
    (δ : K) (value : w 0 * δ + ∑ i, w i.succ * tail i ^ 2 = 0)
    (hD : ∀ u : D, u*u ≠ algebraMap K D δ) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), NoZeroDivisors (L ⊗[K] D) ∧
      ∃ v : Fin (n+1) → L, v ≠ 0 ∧ ∑ i, algebraMap K L (w i) * v i ^ 2 = 0 := by
  let Q := QuadraticAlgebra K δ 0
  have : Fact (∀ r : K, r ^ 2 ≠ δ + 0 * r) := by
    constructor
    intro r eq
    apply hD (algebraMap K D r)
    rw [← map_mul]
    congr 1
    simpa [sq] using eq
  let s : Q := QuadraticAlgebra.omega
  let f := algebraMap K Q
  have square : s ^ 2 = f δ := by simp [sq, s, f, Q, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  have nonzero : s ≠ 0 := by
    intro eq
    have im := congrArg QuadraticAlgebra.im eq
    exact one_ne_zero (show (1:K) = 0 from im)
  refine ⟨Q, inferInstance, inferInstance, (nosquare_iff_quadratic_tensor δ).2 hD,
    Fin.cons s (fun i => f (tail i)), ?_, ?_⟩
  · intro eq
    exact nonzero (by simpa only [Fin.cons_zero, Pi.zero_apply] using congr_fun eq 0)
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, square]
    simpa only [f, map_add, map_sum, map_pow, map_mul, map_zero] using congrArg f value

end KaplanskyQuadric

end

section

namespace KaplanskyQuadric
open scoped TensorProduct
universe u v

/-- A square-root obstruction over an intermediate extension gives a point on
the form over a further extension preserving the algebra with which we started. -/
theorem split_over_composite {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] {n : ℕ} (w : Fin (n+1) → K)
    (witness : ∃ (T : Type u) (_ : Field T) (_ : Algebra K T)
        (tail : Fin n → T) (δ : T),
      NoZeroDivisors (T ⊗[K] A) ∧
      algebraMap K T (w 0) * δ + ∑ i, algebraMap K T (w i.succ) * tail i ^ 2 = 0 ∧
      ∀ x : T ⊗[K] A, x*x ≠ algebraMap T _ δ) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), NoZeroDivisors (L ⊗[K] A) ∧
      ∃ v : Fin (n+1) → L, v ≠ 0 ∧ ∑ i, algebraMap K L (w i) * v i ^ 2 = 0 := by
  obtain ⟨T, fieldT, algT, tail, δ, domain, value, noSquare⟩ := witness
  let B := T ⊗[K] A
  let : Nontrivial B := nontrivial_of_ne (0 : B) (algebraMap T B δ) (by simpa only [zero_mul] using noSquare 0)
  let : IsDomain B := NoZeroDivisors.to_isDomain B
  let : DivisionRing B := divisionRingOfFiniteDimensional T B
  obtain ⟨L, fieldL, algL, h, v, nonzero, point⟩ :=
    split_diagonal_of_no_square (D := B) (fun i => algebraMap K T (w i)) tail δ value noSquare
  let : Algebra K L := ((algebraMap T L).comp (algebraMap K T)).toAlgebra
  let : IsScalarTower K T L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e : (L ⊗[K] A) ≃ₐ[L] L ⊗[T] (T ⊗[K] A) := AlgEquiv.ofLinearEquiv
    (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange K T L L A).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul fun _ _ _ _ => by simp)
  exact ⟨L, fieldL, inferInstance,
    Function.Injective.noZeroDivisors e e.injective (map_zero e) (map_mul e),
    v,nonzero,point⟩

/-- The degenerate diagonal case has a rational isotropic vector. In the
nondegenerate case a nonsquare on a generic affine chart suffices. -/
theorem index_preservation_of_chart
    (chart : ∀ (K : Type) [Field K] [NeZero (2 : K)] (a b c d : K),
      let D : Type := QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d
      NoZeroDivisors D → ∀ w : Fin 7 → K, (∀ i, w i ≠ 0) →
        ∃ (T : Type) (_ : Field T) (_ : Algebra K T) (tail : Fin 6 → T) (δ : T),
          NoZeroDivisors (T ⊗[K] D) ∧
          algebraMap K T (w 0) * δ + ∑ i, algebraMap K T (w i.succ) * tail i ^ 2 = 0 ∧
          ∀ x : T ⊗[K] D, x*x ≠ δ ⊗ₜ[K] (1 : D)) :
    OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1.H2 := by
  classical
  intro K _ _ a b c d domain w
  by_cases hyp : ∀ i, w i ≠ 0
  · obtain ⟨L, fieldL, algL, domainL, v, nonzero, isotropic⟩ :=
      split_over_composite w (chart K a b c d domain w hyp)
    let e := (KaplanskySeed.biquaternion_basechange K L a b c d).symm
    exact ⟨L, fieldL, algebraMap K L, ⟨v, nonzero, isotropic⟩,
      Function.Injective.noZeroDivisors e e.injective (map_zero e) (map_mul e)⟩
  · push Not at hyp
    obtain ⟨i, hi⟩ := hyp
    refine ⟨K, inferInstance, RingHom.id K, ⟨Pi.single i 1, ?_, ?_⟩, domain⟩
    · intro h
      have := congr_fun h i
      simp at this
    · apply Finset.sum_eq_zero
      intro j hj
      by_cases eq : j = i
      · simp [eq, hi]
      · simp [Pi.single_eq_of_ne eq]

end KaplanskyQuadric

end

namespace KaplanskyQuadric

/-- Index preservation for a biquaternion division algebra under splitting a seven-dimensional diagonal form. -/
theorem index_preservation : OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1.H2 :=
  index_preservation_of_chart KaplanskyTrans.biquaternion_chart

end KaplanskyQuadric

section

open Polynomial
open scoped BigOperators

namespace KaplanskyTower

/-- Clearing a common denominator preserves the isotropy of a diagonal form
and preserves a nonzero coordinate of its isotropic vector. -/
theorem clear_denominators {K ι : Type*} [Field K] [Fintype ι]
    (w : ι → K[X]) (z : ι → RatFunc K) (hz : ∃ i, z i ≠ 0)
    (eqn : ∑ i, algebraMap K[X] (RatFunc K) (w i) * z i ^ 2 = 0) :
    ∃ u : ι → K[X], (∃ i, u i ≠ 0) ∧ ∑ i, w i * u i ^ 2 = 0 := by
  classical
  let A := algebraMap K[X] (RatFunc K)
  let D : K[X] := ∏ i, (z i).denom
  let rest (i : ι) := ∏ j ∈ Finset.univ.erase i, (z j).denom
  let u (i : ι) := (z i).num * rest i
  have hD : ∀ i, (z i).denom * rest i = D := fun i =>
    Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have lift (i : ι) : A (u i) = z i * A D := by
    have hn : A (z i).num = z i * A (z i).denom :=
      (div_eq_iff (RatFunc.algebraMap_ne_zero (z i).denom_ne_zero)).mp (z i).num_div_denom
    simp only [u, ← hD i, map_mul, hn, mul_assoc]
  refine ⟨u,?_,?_⟩
  · obtain ⟨i,hi⟩ := hz
    exact ⟨i,mul_ne_zero (RatFunc.num_ne_zero hi)
      (Finset.prod_ne_zero_iff.mpr fun j _ => (z j).denom_ne_zero)⟩
  · apply (RatFunc.algebraMap_injective K)
    change A (∑ i, w i * u i ^ 2) = A 0
    rw [map_zero, map_sum]
    calc
      _ = ∑ i, (A (w i) * z i ^ 2) * (A D)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul,map_pow,lift]
        ring
      _ = (∑ i, A (w i) * z i ^ 2) * (A D)^2 := by rw [Finset.sum_mul]
      _ = 0 := by rw [eqn,zero_mul]

end KaplanskyTower

open Polynomial
open scoped Polynomial BigOperators

namespace Kaplansky

/-- Reducing modulo X forces the first vector into the maximal ideal. Dividing its
entries by X and cancelling a common factor interchanges the two residual forms. -/
theorem polynomial_shift {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    (a : ι → K) (b : κ → K) (ha : ∀ x : ι → K, (∑ i, a i * x i^2) = 0 → ∀ i, x i = 0)
    (x : ι → K[X]) (y : κ → K[X])
    (eqn : (∑ i, C (a i) * x i^2) + X * (∑ j, C (b j) * y j^2) = 0) :
    (∀ i, (x i).coeff 0 = 0) ∧
    (∑ j, C (b j) * y j^2) + X * (∑ i, C (a i) * (x i).divX^2) = 0 := by
  have at0 := congrArg (fun p : K[X] => p.eval 0) eqn
  have zeros : ∀ i, (x i).coeff 0 = 0 := ha _ (by simpa [eval_finsetSum, coeff_zero_eq_eval_zero] using at0)
  have cleared : (∑ i, C (a i) * x i^2) = X^2 * (∑ i, C (a i) * (x i).divX^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := X_mul_divX_add (x i)
    simp only [zeros i, C_0, add_zero] at h
    calc C (a i) * x i ^ 2 = C (a i) * (X * (x i).divX) ^ 2 := by rw [h]
         _ = X ^ 2 * (C (a i) * (x i).divX ^ 2) := by ring
  refine ⟨zeros, (mul_eq_zero.mp (?_ : X * ((∑ j, C (b j) * y j^2) +
    X * (∑ i, C (a i) * (x i).divX^2)) = 0)).resolve_left X_ne_zero⟩
  rw [cleared] at eqn
  rw [mul_add, ← mul_assoc, ← sq, add_comm]
  exact eqn

/-- The two residual forms determine every coefficient of a polynomial isotropic vector. -/
theorem polynomial_springer {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    (a : ι → K) (b : κ → K)
    (ha : ∀ x : ι → K, (∑ i, a i * x i^2) = 0 → ∀ i, x i = 0)
    (hb : ∀ y : κ → K, (∑ j, b j * y j^2) = 0 → ∀ j, y j = 0)
    (x : ι → K[X]) (y : κ → K[X])
    (eqn : (∑ i, C (a i) * x i^2) + X * (∑ j, C (b j) * y j^2) = 0) :
    (∀ i, x i = 0) ∧ (∀ j, y j = 0) := by
  have each (n : ℕ) : (∀ i, (x i).coeff n = 0) ∧ (∀ j, (y j).coeff n = 0) := by
    induction n generalizing x y with
    | zero =>
      obtain ⟨xn, sw⟩ := polynomial_shift a b ha x y eqn
      exact ⟨xn, (polynomial_shift b a hb y (fun i => (x i).divX) sw).1⟩
    | succ n ih =>
      have sw := (polynomial_shift a b ha x y eqn).2
      have divided := (polynomial_shift b a hb y (fun i => (x i).divX) sw).2
      simpa only [coeff_divX] using ih (fun i => (x i).divX) (fun j => (y j).divX) divided
  constructor
  · intro i
    ext n
    simpa using (each n).1 i
  · intro j
    ext n
    simpa using (each n).2 j

end Kaplansky

open Polynomial
open scoped Polynomial BigOperators

namespace Kaplansky

/-- Springer's parity argument for the X-adic valuation of a rational function field.
If two diagonal quadratic forms are anisotropic over K, then their orthogonal sum with
the second form multiplied by X is anisotropic over K(X). -/
theorem springer {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    (a : ι → K) (b : κ → K)
    (ha : ∀ x : ι → K, (∑ i, a i * x i^2) = 0 → ∀ i, x i = 0)
    (hb : ∀ y : κ → K, (∑ j, b j * y j^2) = 0 → ∀ j, y j = 0) :
    ∀ z : ι ⊕ κ → RatFunc K, (∑ i, Sum.elim (fun i => RatFunc.C (a i))
        (fun j => RatFunc.X * RatFunc.C (b j)) i * z i ^ 2) = 0 → ∀ i, z i = 0 := by
  intro z hz i
  by_contra hi
  let w : ι ⊕ κ → K[X] := Sum.elim (fun i => C (a i)) (fun j => X * C (b j))
  have rat : (∑ u, algebraMap K[X] (RatFunc K) (w u) * z u ^ 2) = 0 := by
    simpa only [w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_mul,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X] using hz
  obtain ⟨p, ⟨u, hu⟩, eqn⟩ := KaplanskyTower.clear_denominators w z ⟨i,hi⟩ rat
  have peq : (∑ i, C (a i) * p (.inl i)^2) + X * (∑ j, C (b j) * p (.inr j)^2) = 0 := by
    simpa only [w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.mul_sum,
      mul_assoc] using eqn
  obtain ⟨zeroA, zeroB⟩ := polynomial_springer a b ha hb _ _ peq
  cases u with
  | inl i => exact hu (zeroA i)
  | inr j => exact hu (zeroB j)

end Kaplansky

open scoped BigOperators

namespace Kaplansky

/-- The two ascending blocks of diagonal coordinates, with an explicitly identified target
weight vector. -/
theorem springer_fin {K : Type*} [Field K] {m n : ℕ}
    (a : Fin m → K) (b : Fin n → K) (c : Fin (m+n) → RatFunc K)
    (ha : ∀ x : Fin m → K, (∑ i, a i*x i^2) = 0 → ∀ i, x i = 0)
    (hb : ∀ y : Fin n → K, (∑ i, b i*y i^2) = 0 → ∀ i, y i = 0)
    (left : ∀ i : Fin m, c (i.castAdd n) = RatFunc.C (a i))
    (right : ∀ j : Fin n, c (j.natAdd m) = RatFunc.X * RatFunc.C (b j)) :
    ∀ z : Fin (m+n) → RatFunc K, (∑ i, c i*z i^2) = 0 → ∀ i, z i = 0 := by
  intro z hz i
  rw [Fin.sum_univ_add] at hz
  simp only [left,right] at hz
  have h := springer a b ha hb (Sum.elim (fun i => z (i.castAdd n)) (fun j => z (j.natAdd m)))
    (by simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using hz)
  exact Fin.addCases (fun u => h (.inl u)) (fun v => h (.inr v)) i

theorem anisotropic_one {K : Type*} [Field K] (c : K) (hc : c ≠ 0) :
    ∀ x : Fin 1 → K, (∑ i, (![c] : Fin 1 → K) i*x i^2) = 0 → ∀ i, x i = 0 := by
  intro x eqn i
  have h : c * x 0 ^ 2 = 0 := by simpa using eqn
  simpa only [Subsingleton.elim i 0] using (sq_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left hc))

end Kaplansky

open scoped BigOperators
namespace Kaplansky

/-- One variable suffices over the rational numbers. The two residue forms are
negative definite in four variables, respectively binary with nonsquare discriminant. -/
theorem rational_albert_anisotropic :
    let F := RatFunc ℚ
    let a : F := -1
    let b : F := -1
    let c : F := 2
    let d : F := RatFunc.X
    ∀ v : Fin 6 → F, a*v 0^2 + b*v 1^2 - a*b*v 2^2 - c*v 3^2 - d*v 4^2 + c*d*v 5^2=0 → v=0 := by
  let p : Fin 4 → ℚ := ![-1,-1,-1,-2]
  let q : Fin 2 → ℚ := ![-1,2]
  let t : RatFunc ℚ := RatFunc.X
  let w : Fin 6 → RatFunc ℚ := ![-1,-1,-1,-2,-t,2*t]
  have hp (x : Fin 4 → ℚ) (hx : (∑ i, p i*x i^2)=0) : ∀ i, x i=0 := by
    simp [p, Fin.sum_univ_succ] at hx
    intro i
    apply sq_eq_zero_iff.mp
    have block : x 0 ^ 2 = 0 ∧ x 1 ^ 2 = 0 ∧ x 2 ^ 2 = 0 ∧ x 3 ^ 2 = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [sq_nonneg (x 0),sq_nonneg (x 1),sq_nonneg (x 2),sq_nonneg (x 3)]
    obtain ⟨a,b,c,d⟩ := block
    fin_cases i <;> assumption
  have hq (y : Fin 2 → ℚ) (hy : (∑ i, q i*y i^2)=0) : ∀ i, y i=0 := by
    simp [q, Fin.sum_univ_succ] at hy
    by_cases hn : y 1=0
    · simp [hn] at hy
      intro i
      fin_cases i <;> assumption
    · have hs : (y 0/y 1)^2=2 := by rw [div_pow]; apply (div_eq_iff (pow_ne_zero 2 hn)).mpr; linarith
      have ns : ¬ IsSquare (2 : ℚ) := by norm_num
      exact False.elim (ns ⟨y 0 / y 1, by simpa only [sq] using hs.symm⟩)
  have hw := springer_fin p q w hp hq (by intro i; fin_cases i <;> simp [w,p,t, Fin.castAdd, Fin.castLE])
    (by intro j; fin_cases j <;> simp [w,q,t,Fin.natAdd, mul_comm])
  dsimp only
  intro v hv
  apply _root_.funext
  apply hw v
  simpa [w,t, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using hv

end Kaplansky

open scoped Polynomial

namespace Kaplansky

/-- A rational function is specified by a pair of finite lists of coefficients. -/
theorem countable_ratfunc (K : Type*) [Field K] [Countable K] : Countable (RatFunc K) := by
  let enc (p : Polynomial K) : ℕ →₀ K := p.toFinsupp.coeff
  have pinj : Function.Injective enc := fun _ _ h => Polynomial.toFinsupp_inj.mp (AddMonoidAlgebra.coeff_injective h)
  have : Countable (Polynomial K) := pinj.countable
  apply Function.Injective.countable (f := fun r : RatFunc K => (r.num,r.denom))
  intro r s h
  have hn : r.num = s.num := congrArg Prod.fst h
  have hd : r.denom = s.denom := congrArg Prod.snd h
  calc r = _ := r.num_div_denom.symm
       _ = _ := by rw [hn,hd]
       _ = s := s.num_div_denom

end Kaplansky

namespace KaplanskyCorner
open Matrix

/-- Two noncommuting entries give a noncommutative rank-one corner whenever a
second row is available. -/
theorem corner_of_entries {D n : Type*} [Ring D] [Nontrivial D] [Fintype n] [DecidableEq n]
    (i j : n) (ne : i ≠ j) (x y : D) (nc : x*y ≠ y*x) :
    ∃ e a b : Matrix n n D, e*e=e ∧ e≠0 ∧ e≠1 ∧ e*a*e=a ∧ e*b*e=b ∧ a*b≠b*a := by
  refine ⟨single i i 1,single i i x,single i i y,by simp,?_,?_,by simp,by simp,?_⟩
  · intro eq
    have := congrArg (fun m : Matrix n n D => m i i) eq
    simp at this
  · intro eq
    have := congrArg (fun m : Matrix n n D => m j j) eq
    simp [single,ne] at this
  · intro eq
    apply nc
    have := congrArg (fun m : Matrix n n D => m i i) eq
    simpa using this

/-- Three matrix indices give two noncommuting matrix units in the corner
supported on the first two indices. -/
theorem corner_of_three {D n : Type*} [Ring D] [Nontrivial D] [Fintype n] [DecidableEq n]
    (i j k : n) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
    ∃ e a b : Matrix n n D, e*e=e ∧ e≠0 ∧ e≠1 ∧ e*a*e=a ∧ e*b*e=b ∧ a*b≠b*a := by
  let e : Matrix n n D := single i i 1 + single j j 1
  let a : Matrix n n D := single i i 1
  let b : Matrix n n D := single i j 1
  have right (c : D) : single i i c * (single j j 1 : Matrix n n D) = 0 :=
    single_mul_single_of_ne _ _ _ _ ij _
  have left (c : D) : single j j (1 : D) * single i i c = 0 :=
    single_mul_single_of_ne _ _ _ _ ij.symm _
  refine ⟨e,a,b,?_,?_,?_,?_,?_,?_⟩
  · simp [e,add_mul,mul_add,left,right]
  · intro eq
    have := congrArg (fun m : Matrix n n D => m i i) eq
    simp [e,single,ij.symm] at this
  · intro eq
    have := congrArg (fun m : Matrix n n D => m k k) eq
    simp [e,single,ik,jk] at this
  · simp [e,a,add_mul,mul_add,left,right]
  · simp [e,b,add_mul,mul_add,single_mul_single_of_ne _ _ _ _ ij.symm]
  · intro eq
    have ab : a * b = b := by simp [a,b]
    have ba : b * a = 0 := single_mul_single_of_ne _ _ _ _ ij.symm _
    rw [ab,ba] at eq
    have := congrArg (fun m : Matrix n n D => m i j) eq
    simp [b] at this

end KaplanskyCorner

namespace KaplanskyCorner
open Matrix

/-- A sixteen-dimensional central simple algebra with zero divisors has a
proper nonzero idempotent with noncommutative corner. -/
theorem noncommutative_corner {F A : Type*} [Field F] [Ring A] [Algebra F A]
    [Algebra.IsCentral F A] [IsSimpleRing A] [FiniteDimensional F A]
    (dim : Module.finrank F A = 16) (bad : ¬ NoZeroDivisors A) :
    ∃ e a b : A, e*e=e ∧ e≠0 ∧ e≠1 ∧ e*a*e=a ∧ e*b*e=b ∧ a*b≠b*a := by
  classical
  have : IsArtinianRing A := isArtinian_of_tower F inferInstance
  obtain ⟨n,hn,D,div,alg,finite,⟨φ⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F A
  have two : 2 ≤ n := by
    have hp := NeZero.pos n
    by_contra h
    have eq : n = 1 := by omega
    subst n
    let f := φ.toRingEquiv.trans (Matrix.uniqueRingEquiv : Matrix (Fin 1) (Fin 1) D ≃+* D)
    exact bad (f.injective.noZeroDivisors f (map_zero f) (map_mul f))
  have result : ∃ e a b : Matrix (Fin n) (Fin n) D, e*e=e ∧ e≠0 ∧ e≠1 ∧ e*a*e=a ∧ e*b*e=b ∧ a*b≠b*a := by
    let i : Fin n := ⟨0,by omega⟩
    let j : Fin n := ⟨1,by omega⟩
    have ij : i ≠ j := by intro h; exact Nat.zero_ne_one (Fin.mk.inj h)
    by_cases large : 3 ≤ n
    · let k : Fin n := ⟨2,by omega⟩
      exact corner_of_three i j k ij (by intro h; have := Fin.mk.inj h; omega)
        (by intro h; have := Fin.mk.inj h; omega)
    · by_cases nc : ∃ x y : D, x*y ≠ y*x
      · obtain ⟨x,y,h⟩ := nc
        exact corner_of_entries i j ij x y h
      · push Not at nc
        have : Algebra.IsCentral F (Matrix (Fin n) (Fin n) D) := Algebra.IsCentral.of_algEquiv F _ _ φ
        have onto (x : D) : ∃ r : F, algebraMap F D r = x := by
          have xc : x ∈ Subalgebra.center F D := Subalgebra.mem_center_iff.mpr (fun y => nc y x)
          have mx : scalarAlgHom (Fin n) F x ∈ Subalgebra.center F (Matrix (Fin n) (Fin n) D) := by
            rw [subalgebraCenter_eq_scalarAlgHom_map]
            exact ⟨x,xc,rfl⟩
          obtain ⟨r,hr⟩ := (Algebra.IsCentral.mem_center_iff F).mp mx
          refine ⟨r,?_⟩
          simpa [algebraMap_matrix_apply] using (congrArg (fun m : Matrix (Fin n) (Fin n) D => m i i) hr).symm
        have d1 := (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := F) (E := D)).mpr
          ⟨(algebraMap F D).injective,onto⟩
        have size := φ.toLinearEquiv.finrank_eq
        rw [dim,Module.finrank_matrix,Fintype.card_fin,d1,show n=2 by omega] at size
        exact False.elim ((by decide : ¬16=2*2*1) size)
  obtain ⟨e,a,b,he,e0,e1,ha,hb,nc⟩ := result
  refine ⟨φ.symm e,φ.symm a,φ.symm b,?_,?_,?_,?_,?_,?_⟩
  · rw [←map_mul,he]
  · simpa using e0
  · simpa using e1
  · rw [←map_mul,←map_mul,ha]
  · rw [←map_mul,←map_mul,hb]
  · rw [←map_mul,←map_mul]
    exact φ.symm.injective.ne nc

end KaplanskyCorner

section

namespace KaplanskyCentral
open QuaternionAlgebra

/-- Conjugating by the four quaternion basis units and averaging gives
the real part, whose four translates read off every coordinate. -/
theorem quaternion_averaging {K : Type*} [Field K] [NeZero (2:K)] (a b : K) (ha : a≠0) (hb : b≠0) :
    let Q := QuaternionAlgebra K a 0 b
    ∃ π : Q →ₗ[K] K, ∃ l r h w : Fin 4 → Q,
      π 1 = 1 ∧
      (∀ x, ∑ i,l i*x*r i=algebraMap K Q (π x)) ∧
      (∀ x, ∑ i,π (h i*x) • w i=x) := by
  intro Q
  let e : Fin 4 → Q := ![⟨1,0,0,0⟩,⟨0,1,0,0⟩,⟨0,0,1,0⟩,⟨0,0,0,1⟩]
  let d : Fin 4 → Q := ![⟨1,0,0,0⟩,⟨0,a⁻¹,0,0⟩,⟨0,0,b⁻¹,0⟩,⟨0,0,0,-(a*b)⁻¹⟩]
  let π : Q →ₗ[K] K := reₗ a 0 b
  have two : (2:K) ≠ 0 := NeZero.ne _
  have four : (4:K) ≠ 0 := by convert mul_ne_zero two two using 1; ring
  refine ⟨π,fun i=>(4:K)⁻¹ • e i,d,d,e,rfl,?_,?_⟩
  · intro x
    rcases x with ⟨x₀,x₁,x₂,x₃⟩
    ext <;> simp [Q,Fin.sum_univ_succ,e,d,π,reₗ,QuaternionAlgebra.algebraMap_eq,smul_eq_mul]
      <;> field_simp <;> ring
  · intro x
    rcases x with ⟨x₀,x₁,x₂,x₃⟩
    ext <;> simp [Q,Fin.sum_univ_succ,e,d,π,reₗ,re_mul,smul_eq_mul]
      <;> field_simp

end KaplanskyCentral

end

section

namespace KaplanskyCentral

theorem simple_of_averaging {K A ι : Type*} [Field K] [Ring A] [Algebra K A] [Fintype ι]
    (π : A →ₗ[K] K) (l r h w : ι → A) (one : π 1 = 1)
    (avg : ∀x,∑i,l i*x*r i=algebraMap K A (π x)) (recover : ∀x,∑i, π (h i*x) • w i=x) :
    IsSimpleRing A ∧ Algebra.IsCentral K A := by
  classical
  have : Nontrivial A := nontrivial_of_ne 0 1 (fun h => zero_ne_one ((map_zero π).symm.trans ((congrArg π h).trans one)))
  constructor
  · apply isSimpleRing_iff_isTwoSided_imp.mpr
    refine ⟨inferInstance,?_⟩
    intro I two
    by_cases bot : I=⊥
    · exact Or.inl bot
    right
    obtain ⟨x,hx,x0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot bot
    have somei : ∃ i,π (h i*x) ≠ 0 := by
      by_contra! zero
      exact x0 (by simpa [zero] using (recover x).symm)
    obtain ⟨i,hi⟩ := somei
    apply I.eq_top_of_isUnit_mem (x:=algebraMap K A (π (h i*x))) _ ((isUnit_iff_ne_zero.mpr hi).map _)
    rw [←avg]
    exact I.sum_mem fun z _ => I.mul_mem_right _ (I.mul_mem_left _ (I.mul_mem_left _ hx))
  · constructor
    intro x hx
    refine ⟨π x,?_⟩
    have comm := Subalgebra.mem_center_iff.mp hx
    have base : ∑ i, l i * r i=1 := by simpa [one] using avg 1
    change algebraMap K A (π x)=x
    rw [←avg]
    calc
      _ = ∑ i,x*(l i*r i) := Finset.sum_congr rfl fun i _ => by rw [comm (l i),mul_assoc]
      _ = x := by rw [←Finset.mul_sum,base,mul_one]

end KaplanskyCentral

end

section

namespace KaplanskyCentral
open scoped TensorProduct
open TensorProduct

theorem tensor_averaging {K A B ι κ : Type*} [Field K] [Ring A] [Algebra K A]
    [Ring B] [Algebra K B] [Fintype ι] [Fintype κ]
    (π : A →ₗ[K] K) (l r h w : ι → A) (one : π 1 = 1)
    (avg : ∀x,∑i,l i*x*r i=algebraMap K A (π x)) (recover : ∀x,∑i,π (h i*x) • w i=x)
    (ρ : B →ₗ[K] K) (L R H W : κ → B) (one' : ρ 1 = 1)
    (avg' : ∀x,∑i,L i*x*R i=algebraMap K B (ρ x)) (recover' : ∀x,∑i,ρ (H i*x) • W i=x) :
    let T := A ⊗[K] B
    ∃ τ : T →ₗ[K] K, ∃ l' r' h' w' : ι × κ → T,
      τ 1 = 1 ∧ (∀ x,∑ i,l' i*x*r' i=algebraMap K T (τ x)) ∧
      (∀ x,∑ i,τ (h' i*x) • w' i=x) := by
  classical
  intro T
  let τ : T →ₗ[K] K := (TensorProduct.lid K K).toLinearMap.comp (TensorProduct.map π ρ)
  have tm (x : A) (y : B) : τ (x ⊗ₜ[K] y)=π x*ρ y := rfl
  let tensor (f : ι→A) (g : κ→B) (i : ι×κ) : T := f i.1 ⊗ₜ[K] g i.2
  refine ⟨τ,tensor l L,tensor r R,tensor h H,tensor w W,?_,?_,?_⟩
  · rw [Algebra.TensorProduct.one_def,tm,one,one',one_mul]
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [mul_add,add_mul,Finset.sum_add_distrib,hx,hy]
    | tmul x y =>
      simp only [T,tensor,Fintype.sum_prod_type,Algebra.TensorProduct.tmul_mul_tmul,tm]
      simp_rw [←TensorProduct.tmul_sum,avg',←TensorProduct.sum_tmul,avg]
      rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul_smul,←Algebra.TensorProduct.one_def,Algebra.algebraMap_eq_smul_one]
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [mul_add,add_smul,Finset.sum_add_distrib,hx,hy]
    | tmul x y =>
      simp only [T,tensor,Fintype.sum_prod_type,Algebra.TensorProduct.tmul_mul_tmul,tm]
      simp_rw [←TensorProduct.smul_tmul_smul,←TensorProduct.tmul_sum,recover',←TensorProduct.sum_tmul,recover]

end KaplanskyCentral

end

section

namespace KaplanskyCentral
open scoped TensorProduct

theorem quaternion_central_simple {K : Type*} [Field K] [NeZero (2:K)] (a b : K)
    (ha : a≠0) (hb : b≠0) : let Q := QuaternionAlgebra K a 0 b
    IsSimpleRing Q ∧ Algebra.IsCentral K Q := by
  obtain ⟨π,l,r,h,w,one,avg,rec⟩ := quaternion_averaging a b ha hb
  exact simple_of_averaging π l r h w one avg rec

/-- The tensor product of the two symbol quaternions is central simple,
including when either symbol quaternion splits. -/
theorem biquaternion_central_simple {K : Type*} [Field K] [NeZero (2:K)] (a b c d : K)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    let A := QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d
    IsSimpleRing A ∧ Algebra.IsCentral K A := by
  obtain ⟨π,l,r,h,w,one,avg,rec⟩ := quaternion_averaging a b ha hb
  obtain ⟨ρ,L,R,H,W,one',avg',rec'⟩ := quaternion_averaging c d hc hd
  obtain ⟨τ,l',r',h',w',onet,avgt,rect⟩ := tensor_averaging π l r h w one avg rec
    ρ L R H W one' avg' rec'
  exact simple_of_averaging τ l' r' h' w' onet avgt rect

end KaplanskyCentral

end

open scoped TensorProduct
namespace KaplanskyAlbert

theorem pure_pair_isUnit {F : Type*} [Field F] (a b c d : F)
    (anis : ∀ v : Fin 6 → F, a*v 0^2 + b*v 1^2 - a*b*v 2^2 - c*v 3^2 - d*v 4^2 + c*d*v 5^2 = 0 → v=0)
    (u : QuaternionAlgebra F a 0 b) (v : QuaternionAlgebra F c 0 d) (hu : u.re = 0) (hv : v.re = 0)
    (nonzero : u ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) +
      (1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] v ≠ 0) :
    IsUnit (u ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) + (1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] v) := by
  let U := QuaternionAlgebra F a 0 b
  let V := QuaternionAlgebra F c 0 d
  let s := a*u.imI^2 + b*u.imJ^2 - a*b*u.imK^2
  let t := c*v.imI^2 + d*v.imJ^2 - c*d*v.imK^2
  have ns : s - t ≠ 0 := by
    intro h
    let w : Fin 6 → F := ![u.imI,u.imJ,u.imK,v.imI,v.imJ,v.imK]
    have hw : w=0 := anis w (by
      change s - c*v.imI^2 - d*v.imJ^2 + c*d*v.imK^2=0
      dsimp [t] at h
      linear_combination h)
    have u0 : u=0 := by
      apply QuaternionAlgebra.ext hu
      · exact congrFun hw 0
      · exact congrFun hw 1
      · exact congrFun hw 2
    have v0 : v=0 := by
      apply QuaternionAlgebra.ext hv
      · exact congrFun hw 3
      · exact congrFun hw 4
      · exact congrFun hw 5
    exact nonzero (by rw [u0,v0]; simp)
  have us : u*u = algebraMap F U s := by ext <;> simp [U,s,hu,QuaternionAlgebra.algebraMap_eq] <;> ring
  have vt : v*v = algebraMap F V t := by ext <;> simp [V,t,hv,QuaternionAlgebra.algebraMap_eq] <;> ring
  let l := u ⊗ₜ[F] (1 : V)
  let r := (1 : U) ⊗ₜ[F] v
  have commute : Commute l r := by simp [Commute,SemiconjBy,l,r,Algebra.TensorProduct.tmul_mul_tmul]
  have pm : Commute (l+r) (l-r) := (Commute.refl l).add_left commute.symm |>.sub_right (commute.add_left (Commute.refl r))
  have prod : (l+r)*(l-r) = algebraMap F (U ⊗[F] V) (s-t) := by
    rw [add_mul,mul_sub,mul_sub,commute.symm.eq]
    have h : (l*l-l*r)+(l*r-r*r) = l*l-r*r := by abel
    rw [h,map_sub]
    congr 1
    · simp only [l,Algebra.TensorProduct.tmul_mul_tmul, mul_one,us,Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul,TensorProduct.tmul_smul]
      rfl
    · simp only [r,Algebra.TensorProduct.tmul_mul_tmul, mul_one,vt,Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul]
      rfl
  exact (pm.isUnit_mul_iff.mp (prod ▸ (isUnit_iff_ne_zero.mpr ns).map (algebraMap F (U ⊗[F] V)))).1

set_option maxHeartbeats 1200000 in
theorem skew_involution {F : Type*} [Field F] [NeZero (2 : F)] (a b c d : F)
    (anis : ∀ v : Fin 6 → F, a*v 0^2 + b*v 1^2 - a*b*v 2^2 - c*v 3^2 - d*v 4^2 + c*d*v 5^2 = 0 → v=0) :
    let D := QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d
    ∃ γ : D → D, Function.Involutive γ ∧ (∀ x y, γ (x*y)=γ y*γ x) ∧ (∀ x y, γ (x-y)=γ x-γ y) ∧
      γ 0=0 ∧ ∀ w : D, γ w = -w → w ≠ 0 → IsUnit w := by
  let conjugation (u v : F) : QuaternionAlgebra F u 0 v →ₗ[F] QuaternionAlgebra F u 0 v :=
    { toFun := star, map_add' := star_add, map_smul' := QuaternionAlgebra.star_smul' }

  let conjugate : (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d) →ₗ[F]
      (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d) :=
    TensorProduct.map (conjugation a b) (conjugation c d)

  have conjugate_tmul (u : QuaternionAlgebra F a 0 b) (v : QuaternionAlgebra F c 0 d) :
      conjugate (u ⊗ₜ[F] v) = star u ⊗ₜ[F] star v := rfl

  have conjugate_involutive : Function.Involutive (conjugate) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => simp [conjugate_tmul]
    | add x y hx hy => simp [hx,hy]

  have conjugate_mul (x y : QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d) :
      conjugate (x*y) = conjugate y * conjugate x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x z hx hz => simp [add_mul, mul_add, hx,hz]
    | tmul u v =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x z hx hz => simp [add_mul,mul_add,hx,hz]
      | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul,conjugate_tmul]

  have skew_normal
      (x : QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d)
      (hx : conjugate x = -x) :
      ∃ (u : QuaternionAlgebra F a 0 b) (v : QuaternionAlgebra F c 0 d),
        u.re=0 ∧ v.re=0 ∧ x = u ⊗ₜ[F] 1 + 1 ⊗ₜ[F] v := by
    let B := (QuaternionAlgebra.basisOneIJK a 0 b).tensorProduct (QuaternionAlgebra.basisOneIJK c 0 d)
    have invariant (i j : Fin 4) (same : (i=0 ↔ j=0)) (z : QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d) :
        B.repr (conjugate z) (i,j) = B.repr z (i,j) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simpa using congrArg₂ (·+·) hx hy
      | tmul u v =>
        rw [conjugate_tmul]
        simp only [B,Module.Basis.tensorProduct_repr_tmul_apply,QuaternionAlgebra.coe_basisOneIJK_repr]
        fin_cases i <;> fin_cases j <;> simp at same ⊢
    have vanish (i j : Fin 4) (same : (i=0 ↔ j=0)) : B.repr x (i,j)=0 := by
      have h := invariant i j same x
      rw [hx,map_neg] at h
      change -B.repr x (i,j) = B.repr x (i,j) at h
      have h2 : 2 * B.repr x (i,j) = 0 := by
        rw [two_mul]
        exact (congrArg (· + B.repr x (i,j)) h).symm.trans (neg_add_cancel _)
      exact (mul_eq_zero.mp h2).resolve_left (NeZero.ne 2)
    let u : QuaternionAlgebra F a 0 b := ⟨0,B.repr x (1,0),B.repr x (2,0),B.repr x (3,0)⟩
    let v : QuaternionAlgebra F c 0 d := ⟨0,B.repr x (0,1),B.repr x (0,2),B.repr x (0,3)⟩
    refine ⟨u,v,rfl,rfl,B.repr.injective ?_⟩
    ext ⟨i,j⟩
    simp only [map_add,Finsupp.coe_add,Pi.add_apply]
    change B.repr x (i,j) = _ + _
    simp only [B,Module.Basis.tensorProduct_repr_tmul_apply,QuaternionAlgebra.coe_basisOneIJK_repr]
    fin_cases i <;> fin_cases j <;> simp [u,v]
    all_goals try (apply vanish; decide)
    all_goals rfl
  refine ⟨conjugate,conjugate_involutive,conjugate_mul,map_sub _,map_zero _,?_⟩
  intro w skew nz
  obtain ⟨u,v,hu,hv,eq⟩ := skew_normal w skew
  rw [eq] at nz ⊢
  exact pure_pair_isUnit a b c d anis u v hu hv nz

end KaplanskyAlbert

namespace Kaplansky

/-- A nonzero element generates a simple ring as a two-sided ideal. -/
theorem simple_sandwich {A : Type*} [Ring A] [IsSimpleRing A] {x y : A} (hy : y ≠ 0)
    (kill : ∀ t : A, x*t*y = 0) : x = 0 := by
  let S : Set A := {z | ∀ t : A, x*t*z=0}
  let I := TwoSidedIdeal.mk' S (by intro t; exact mul_zero _)
    (by intro a b ha hb t; rw [mul_add,ha t,hb t,add_zero])
    (by intro a ha t; rw [mul_neg,ha t,neg_zero])
    (by intro a b hb t; simpa only [mul_assoc] using hb (t*a))
    (by intro a b ha t; rw [← mul_assoc,ha t,zero_mul])
  have one : (1 : A) ∈ I := IsSimpleRing.one_mem_of_ne_zero_mem I hy
    (by simpa only [I,TwoSidedIdeal.mem_mk',S,Set.mem_ofPred_eq] using kill)
  have all : ∀ t : A, x*t*1=0 := by simpa only [I,TwoSidedIdeal.mem_mk',S,Set.mem_ofPred_eq] using one
  simpa using all 1

/-- A proper matrix corner that is noncommutative forces a nonzero skew nonunit
under any ring involution. -/
theorem skew_nonunit_of_corner {A : Type*} [Ring A] [IsSimpleRing A]
    (γ : A → A) (invol : Function.Involutive γ) (rev : ∀ x y, γ (x*y) = γ y * γ x)
    (sub : ∀ x y, γ (x-y) = γ x - γ y) (zero : γ 0=0)
    {e a b : A} (ee : e*e=e) (e0 : e≠0) (e1 : e≠1)
    (ha : e*a*e=a) (hb : e*b*e=b) (noncomm : a*b≠b*a) :
    ∃ w : A, γ w = -w ∧ w≠0 ∧ ¬IsUnit w := by
  classical
  by_contra! none
  let Z := fun t : A => e*t*γ e
  have fixedLeft (t : A) : e*Z t=Z t := by simp only [Z, ← mul_assoc,ee]
  have twist (t : A) : γ (Z t)=Z (γ t) := by simp only [Z,rev,invol e, mul_assoc]
  have symm (t : A) : γ (Z t)=Z t := by
    by_contra notsym
    let w := Z t-γ (Z t)
    have skew : γ w = -w := by simp only [w,sub,invol (Z t),neg_sub]
    have wne : w≠0 := sub_ne_zero.mpr (Ne.symm notsym)
    have uw := none w skew wne
    apply e1
    apply uw.mul_right_cancel
    simp only [w,mul_sub,twist,fixedLeft,one_mul]
  have sides {u : A} (hu : e*u*e=u) : e*u=u ∧ u*e=u := by
    constructor
    · calc e*u = e*(e*u*e) := congrArg (e*·) hu.symm
           _ = u := by simpa only [← mul_assoc,ee] using hu
    · calc u*e = (e*u*e)*e := congrArg (·*e) hu.symm
           _ = u := by simpa only [mul_assoc,ee] using hu
  have adj {u : A} (ul : e*u=u) (ur : u*e=u) (t : A) : u*Z t=Z t*γ u := by
    have prod : Z (u*t) = u*Z t := by simp only [Z,← mul_assoc,ul,ur]
    calc u*Z t = γ (u*Z t) := by simpa only [← prod] using (symm (u*t)).symm
         _ = Z t*γ u := by rw [rev,symm]
  obtain ⟨al,ar⟩ := sides ha
  obtain ⟨bl,br⟩ := sides hb
  have commute (t : A) : (a*b)*Z t = (b*a)*Z t := by
    have l : e*(b*a)=b*a := by rw [← mul_assoc,bl]
    have r : b*a*e=b*a := by rw [mul_assoc,ar]
    calc (a*b)*Z t = a*(b*Z t) := mul_assoc ..
         _ = a*(Z t*γ b) := by rw [adj bl br]
         _ = Z t*γ (b*a) := by rw [← mul_assoc,adj al ar,mul_assoc,rev]
         _ = (b*a)*Z t := (adj l r t).symm
  apply noncomm
  apply sub_eq_zero.mp
  apply simple_sandwich (x := a*b-b*a) (y := γ e) (fun h => e0 (invol.injective (h.trans zero.symm)))
  intro t
  have r₁ : a*b*e=a*b := by rw [mul_assoc,br]
  have r₂ : b*a*e=b*a := by rw [mul_assoc,ar]
  have h := commute t
  simp only [Z, ← mul_assoc,r₁,r₂] at h
  simpa only [sub_mul,sub_eq_zero] using h

end Kaplansky

/-- If every nonzero skew element is invertible, a nonsimple-as-division algebra
cannot supply its characteristic noncommuting proper corner. -/
theorem Kaplansky.noZeroDivisors_of_skew_units {A : Type*} [Ring A] [IsSimpleRing A]
    (corner : ¬NoZeroDivisors A → ∃ e a b : A, e*e=e ∧ e≠0 ∧ e≠1 ∧
      e*a*e=a ∧ e*b*e=b ∧ a*b≠b*a)
    (skew : ∃ γ : A → A, Function.Involutive γ ∧ (∀ x y,γ (x*y)=γ y*γ x) ∧
      (∀ x y,γ (x-y)=γ x-γ y) ∧ γ 0=0 ∧ (∀ w, γ w = -w → w≠0 → IsUnit w)) :
    NoZeroDivisors A := by
  classical
  by_contra h
  obtain ⟨e,a,b,ee,h0,h1,ha,hb,hn⟩ := corner h
  obtain ⟨γ,hi,hm,hs,hz,units⟩ := skew
  obtain ⟨w,hw,nw,nu⟩ := Kaplansky.skew_nonunit_of_corner γ hi hm hs hz ee h0 h1 ha hb hn
  exact nu (units w hw nw)

open scoped TensorProduct

namespace Kaplansky

/-- Anisotropy forces each Hilbert symbol parameter to be nonzero. -/
theorem albert_parameters_nonzero {F : Type*} [Field F] {a b c d : F}
    (anis : ∀ v : Fin 6 → F, a*v 0^2 + b*v 1^2 - a*b*v 2^2 -c*v 3^2 -d*v 4^2 + c*d*v 5^2=0 → v=0) :
    a≠0 ∧ b≠0 ∧ c≠0 ∧ d≠0 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro ha
    have h := anis ![1,0,0,0,0,0] (by simp [ha])
    simpa using congrFun h 0
  · intro hb
    have h := anis ![0,1,0,0,0,0] (by simp [hb])
    simpa using congrFun h 1
  · intro hc
    have h := anis ![0,0,0,1,0,0] (by simp [hc])
    simpa using congrFun h 3
  · intro hd
    have h := anis ![0,0,0,0,1,0] (by simp [hd])
    simpa using congrFun h 4

/-- The sixteen products of the four distinguished quaternion basis vectors form a basis. -/
theorem biquaternion_finrank (F : Type*) [Field F] (a b c d : F) :
    Module.finrank F (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d) = 16 := by
  let B := (QuaternionAlgebra.basisOneIJK a 0 b).tensorProduct
    (QuaternionAlgebra.basisOneIJK c 0 d)
  rw [Module.finrank_eq_card_basis B]
  decide

end Kaplansky

open scoped TensorProduct

namespace KaplanskyAlbert

/-- Albert's division criterion for a tensor product of two quaternion algebras:
anisotropy of the six-dimensional pure form implies there are no zero divisors. -/
theorem division_of_anisotropic {F : Type*} [Field F] [NeZero (2:F)] (a b c d : F)
    (anis : ∀ v : Fin 6 → F, a*v 0^2 + b*v 1^2 - a*b*v 2^2 - c*v 3^2 - d*v 4^2 + c*d*v 5^2=0 → v=0) :
    NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d) := by
  let A := QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d
  obtain ⟨ha,hb,hc,hd⟩ := Kaplansky.albert_parameters_nonzero anis
  obtain ⟨simple, central⟩ := KaplanskyCentral.biquaternion_central_simple a b c d ha hb hc hd
  have dim := Kaplansky.biquaternion_finrank F a b c d
  have finite : FiniteDimensional F A := Module.finite_of_finrank_pos (by rw [show Module.finrank F A=16 from dim]; decide)
  exact Kaplansky.noZeroDivisors_of_skew_units
    (KaplanskyCorner.noncommutative_corner (F := F) dim) (skew_involution a b c d anis)

end KaplanskyAlbert

open scoped TensorProduct
namespace KaplanskyAlbert

/-- The biquaternion division algebra `(−1,−1) ⊗ (2,t)` over the one-variable
rational function field over the rationals. -/
theorem rational_seed :
    NoZeroDivisors (QuaternionAlgebra (RatFunc ℚ) (-1) 0 (-1) ⊗[RatFunc ℚ]
      QuaternionAlgebra (RatFunc ℚ) 2 0 RatFunc.X) :=
  division_of_anisotropic _ _ _ _ Kaplansky.rational_albert_anisotropic

/-- An explicit countable characteristic-zero starting field for the quadratic-form tower. -/
theorem seed : ∃ (F : Type) (_ : Field F) (_ : NeZero (2:F)) (_ : Countable F) (a b c d : F),
    NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d) :=
  ⟨RatFunc ℚ, inferInstance, inferInstance, Kaplansky.countable_ratfunc ℚ, -1, -1, 2, RatFunc.X,
    rational_seed⟩

end KaplanskyAlbert

end

namespace KaplanskyAlbert

/-- The resulting characteristic-not-two field has an anisotropic six-dimensional
form, while every form of greater dimension is isotropic. -/
theorem isUInvariant_six : KaplanskyUInvariant.IsUInvariant 6 := by
  obtain ⟨G, fieldG, trans, system, a, b, c, d, two, division, isotropic⟩ :=
    OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1.exists_tower_of_hyps seed KaplanskyQuadric.index_preservation
  exact OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1.isUInvariant_six_of_tower G trans a b c d division isotropic

end KaplanskyAlbert

theorem OMA.solution : type_of% @KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture := by
  intro conjecture
  obtain ⟨k, hk⟩ := conjecture 6 KaplanskyAlbert.isUInvariant_six
  rcases Nat.lt_or_ge k 3 with small | large
  · interval_cases k <;> omega
  · have lower := Nat.pow_le_pow_right (by decide : 1 ≤ 2) large
    omega
