import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul

/-!
# MathOverflow 69015: two claims about a matrix iteration

Source: https://mathoverflow.net/questions/69015/maximization-of-a-matrix-product-by-iterative-methods
Question by BharatRam, June 28, 2011.
Known power-iteration discussion: answers by theja and Pietro Majer, with
comments by Denis Serre and Pietro Majer, June 28, 2011.

At a unit vector y the procedure chooses a unit vector z globally maximizing
z^T A y and then replaces y by z. These definitions state the optimization
step itself, without assuming any formula for its maximizer. The two claims
are that every fixed point globally maximizes x^T A x on the unit sphere,
and that the optimized linear objective is nondecreasing between steps.

Unit vectors use the sum of squares of coordinates in EuclideanSpace, so the
constraint is the Euclidean sphere rather than the supremum-norm sphere.
The proof also supplies a certificate that a fixed point need not be a local
maximizer, even for a symmetric positive-definite matrix.
-/

open Matrix
open scoped BigOperators

namespace OMA.S_mo_69015

def unit {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∑ i, (x i) ^ 2 = 1

def bilinear {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  dotProduct (fun i => z i) (A.mulVec (fun i => y i))

def objective {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := bilinear A x x

def Step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) : Prop :=
  unit y ∧ unit z ∧ ∀ w, unit w → bilinear A w y ≤ bilinear A z y

def FixedPointClaim : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (A : Matrix (Fin n) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)), Step A y y →
    ∀ x, unit x → objective A x ≤ objective A y

def MonotonicityClaim : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (A : Matrix (Fin n) (Fin n) ℝ)
    (y z w : EuclideanSpace ℝ (Fin n)), Step A y z → Step A z w →
    bilinear A z y ≤ bilinear A w z

def claim : Prop := FixedPointClaim ∧ MonotonicityClaim

theorem main : claim := by
  sorry

end OMA.S_mo_69015
