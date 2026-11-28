import Mathlib

/-!
# Exact norm of a symmetric sweep of hyperplane projections

Source: dave2d, https://mathoverflow.net/questions/316603 (CC BY-SA).
Credit: @connoranderson.

For a real matrix A with independent unit columns, remove each column
direction in turn. If Q denotes the forward sweep, the palindromic product in
the question is QᵀQ since the central projection is idempotent. The unit lower
triangular matrix L uses the strict lower triangle of the column Gram matrix.
The formula computes the norm from the single matrix (Aᵀ)⁻¹L and shows why the
norm can approach one. It applies in particular to positive definite A.
-/

namespace OMA.S_mo_316603
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def projection {n : ℕ} (A : Mat n) (j : Fin n) : Mat n :=
  1-vecMulVec (A.col j) (A.col j)
noncomputable def sweep {n : ℕ} (A : Mat n) : ℕ → Mat n
  | 0 => 1
  | m+1 => if h : m<n then projection A ⟨m,h⟩ * sweep A m else sweep A m
noncomputable def lowerGram {n : ℕ} (A : Mat n) : Mat n := fun i j =>
  if j < i then A.col i ⬝ᵥ A.col j else if i=j then 1 else 0
noncomputable def opNorm {n : ℕ} (M : Mat n) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

theorem main : ∀ (n : ℕ) (_ : 0<n) (A : Mat n), IsUnit A.det →
    (∀ i, A.col i ⬝ᵥ A.col i=1) →
    let Q := sweep A n
    let P := Q.transpose*Q
    let T := A.transpose⁻¹*lowerGram A
    (∀ i, projection A i * projection A i=projection A i) ∧
    opNorm P = 1 - (opNorm T)⁻¹^2 ∧ opNorm P < 1 := by
  sorry

end OMA.S_mo_316603
