import Mathlib

/-!
# Integrality of the inverse Catalan triangle (OEIS A127767)

Paul Barry, January 28, 2007. Source: https://oeis.org/A127767
Lean formalization by @city-ships.

Rows and columns start at zero. Each leading block is lower triangular with
a nonzero diagonal. Its inverse agrees with the inverse of each larger block
on the shared leading rows and columns, so these blocks cover the full triangle.
-/

namespace OMA.S_oeis_a127767

/-- The leading block on indices 0 through N of Barry's rational matrix. -/
def triangle (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ := fun i j =>
  if j.val ≤ i.val ∧ i.val ≤ 2 * j.val then (catalan i.val : ℚ)⁻¹ else 0

/-- Every entry of the inverse triangle is an integer. -/
theorem main : ∀ (N : ℕ) (i j : Fin (N + 1)),
    ∃ z : ℤ, (triangle N)⁻¹ i j = (z : ℚ) := by
  sorry

end OMA.S_oeis_a127767
