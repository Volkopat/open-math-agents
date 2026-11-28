import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Data.Real.Basic

/-!
# Matrix inverse-Hadamard condition and triangularity

Source: https://mathoverflow.net/questions/406611
Question author: Bee. Credit for formalization: @etaubman.

The source conjectures that a nonnegative matrix with zero diagonal satisfying
the inverse-transpose Hadamard condition must be upper or lower triangular.
The determinant hypothesis makes the source's inverse well-defined.
The associated proof also refutes triangularity after every simultaneous
permutation of rows and columns, the refinement discussed in the source thread.
-/

namespace OMA.S_mo_406611

open Matrix

theorem main :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, 0 ≤ A i j) →
      (∀ i, A i i = 0) →
      (1 - A).det ≠ 0 →
      Matrix.hadamard ((1 - A)⁻¹)ᵀ A = 0 →
      A.IsUpperTriangular ∨ A.IsLowerTriangular := by
  sorry

end OMA.S_mo_406611
