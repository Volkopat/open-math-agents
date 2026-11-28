import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace OMA.S_oeis_a372314

/-- The `(2*k - 3) × (2*k - 3)` Jacobi-symbol matrix `[J(i^2 + 3*i*j + 2*j^2, 2*k + 1)]`
for `1 < i, j < 2*k` (i.e., `2 ≤ i, j ≤ 2*k - 1`). -/
def sunJacobiMatrix (k : ℕ) : Matrix (Fin (2 * k - 2)) (Fin (2 * k - 2)) ℤ :=
  Matrix.of (fun i j =>
    jacobiSym (((i.val + 2 : ℕ) : ℤ) ^ 2 +
      3 * ((i.val + 2 : ℕ) : ℤ) * ((j.val + 2 : ℕ) : ℤ) +
      2 * ((j.val + 2 : ℕ) : ℤ) ^ 2) (2 * k + 1))

/-- OEIS A372314 Conjecture 1(i) (Zhi-Wei Sun): for every positive integer `n`,
if `a(2*n) = det [J(i^2 + 3*i*j + 2*j^2, 4*n + 1)]_{1 < i, j < 4*n}` is nonzero,
then `4*n + 1` is a sum of two squares. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (sunJacobiMatrix (2 * n)).det ≠ 0 →
      ∃ x y : ℕ, x ^ 2 + y ^ 2 = 4 * n + 1 := by
  sorry

end OMA.S_oeis_a372314
