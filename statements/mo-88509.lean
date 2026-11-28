import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exact minimum rank with nonsingular antisymmetric part

Source: https://mathoverflow.net/questions/88509/minimum-rank-of-a-general-matrix
Question by lugica; rank-subadditivity hint by David E. Speyer in the source comments.
Credit: @etaubman

The source does not specify the base field. This formalization uses the standard real-matrix
reading. The antisymmetric part is represented by A - Aᵀ; multiplying it by 1/2, as in
another standard convention, does not change nonsingularity over the reals.

There are no admissible matrices of odd order. In every even order 2k the minimum rank
is exactly k: subadditivity gives 2k = rank(A-Aᵀ) <= 2 rank(A), and the block matrix
[0 I; 0 0] attains equality. The formalization uses Mathlib's Matrix.rank and determinant.
-/

open Matrix

namespace OMA.S_mo_88509

theorem main :
    (∀ m : ℕ, ∀ A : Matrix (Fin m) (Fin m) ℝ,
      (A - Aᵀ).det ≠ 0 → Even m ∧ m ≤ 2 * A.rank) ∧
    (∀ k : ℕ, ∃ A : Matrix (Fin (k + k)) (Fin (k + k)) ℝ,
      (A - Aᵀ).det ≠ 0 ∧ A.rank = k) := by
  sorry

end OMA.S_mo_88509
