import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Maximal minors of a tensor square

Source: https://mathoverflow.net/questions/444295/maximal-minors-of-tensor-product
Question by Ben, April 6, 2023; edited April 10, 2023. CC BY-SA 4.0.
Credit: @etaubman

The source asks whether all maximal minors in {0,1,-1} are preserved by
A tensor A. Dimensions are nonnegative integers. A column embedding selects
a maximal minor; allowing every ordering is equivalent because the allowed
set is closed under sign changes. The tensor square uses row-major indexing
through the standard equivalence Fin r x Fin r = Fin (r*r).
-/

namespace OMA.S_mo_444295

def smallDet (z : ℤ) : Prop := z = 0 ∨ z = 1 ∨ z = -1

def tensorSquare {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r * r)) (Fin (n * n)) ℤ :=
  (Matrix.kronecker A A).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

theorem main : ∀ (r n : ℕ), r ≤ n → ∀ A : Matrix (Fin r) (Fin n) ℤ,
  (∀ c : Fin r ↪ Fin n, smallDet (A.submatrix id c).det) →
    ∀ c : Fin (r * r) ↪ Fin (n * n), smallDet ((tensorSquare A).submatrix id c).det := by
  sorry

end OMA.S_mo_444295
