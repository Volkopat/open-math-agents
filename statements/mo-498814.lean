import Mathlib

/-!
# A Lipschitz choice of covariance square root

Source: Roy, https://mathoverflow.net/questions/498814 (CC BY-SA 4.0).
Credit: @connoranderson.

Centered square-integrable real random variables are vectors in the real
inner-product space L². Their covariance is the Gram matrix, and the squared
distance for any coupling is the sum of squared L² distances of coordinates.
We use the usual Frobenius norm, taking the square root of the sum of squares;
the source's one-dimensional example and Wasserstein formulation use this
homogeneous convention. The bound holds for every finite dimension and every
coupling. For the principal positive square root the constant √2 is optimal
already in dimension two.
-/

namespace OMA.S_mo_498814
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.L2Operator

def froSq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j)^2

noncomputable def stdRoot {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Fin n → H) : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (Matrix.gram ℝ X)

theorem main :
    (∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (X Y : Fin n → H),
      (stdRoot X).PosSemidef ∧ stdRoot X * (stdRoot X)ᵀ = Matrix.gram ℝ X ∧
      froSq (stdRoot X-stdRoot Y) ≤ 2 * ∑ i, ‖X i-Y i‖^2) ∧
    (∀ C : ℝ, C < 2 → ∃ X Y : Fin 2 → ℝ,
      C * (∑ i, ‖X i-Y i‖^2) < froSq (stdRoot X-stdRoot Y)) := by
  sorry
end OMA.S_mo_498814
