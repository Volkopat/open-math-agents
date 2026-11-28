import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.GroupTheory.Perm.Sign

/-!
# Nonnegativity of a Hermitian form on orthonormal product states

Source: https://mathoverflow.net/questions/485529 (question by meler).
Credit: @aghilliotti

The double sum is over the permutation-indexed subblock of the tensor-product
basis. All rows and columns outside that subblock make zero contribution.
The columns of the square matrix `U` are the orthonormal basis in the question.
-/

namespace OMA.S_mo_485529

open scoped BigOperators

/-- The coefficient of the product vector on the basis tensor indexed by `σ`. -/
def productCoeff {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  ∏ i, U (σ i) i

/-- The real matrix entry between the basis tensors indexed by `σ` and `ρ`. -/
def formEntry {n : ℕ} (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (σ ρ : Equiv.Perm (Fin n)) : ℝ :=
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  (A (σ i) (σ j) * A (ρ j) (ρ k) - A (σ j) (σ k) * A (ρ i) (ρ j)) ^ 2 *
    ((↑(Equiv.Perm.sign (σ * ρ)) : ℤ) : ℝ)

theorem main : ∀ (n : ℕ) (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = A j i)
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1),
    0 ≤ (∑ σ : Equiv.Perm (Fin n), ∑ ρ : Equiv.Perm (Fin n),
      star (productCoeff U σ) * (formEntry hn A σ ρ : ℂ) * productCoeff U ρ).re := by
  sorry

end OMA.S_mo_485529
