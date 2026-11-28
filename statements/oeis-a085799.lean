import Mathlib

/-!
# OEIS A085799

Fried's determinant formula and Lajos's permutation-count conjecture. See
Theorem 5 and Corollary 1 of https://arxiv.org/abs/2606.09913.
-/

open scoped BigOperators Matrix

namespace OMA.S_oeis_a085799

/-- The symmetric matrix with entries given by the distance between two squares. -/
def squareDistance (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => |((i.val : ℚ) + 1)^2 - ((j.val : ℚ) + 1)^2|

/-- The determinant sequence A085799. -/
def a (n : ℕ) : ℚ := (squareDistance n).det

/-- The number of ordered selections of distinct entries. -/
noncomputable def permutationCount (m r : ℕ) : ℕ :=
  Fintype.card (Fin r ↪ Fin m)

/-- The factorial formula for the determinant and the permutation-count identity. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → a n = (-1 : ℚ)^(n-1) * ((n : ℚ)+1)/2 *
      ((2*n-1).factorial : ℚ) / ((n-2).factorial : ℚ)) ∧
    (∀ n : ℕ, 0 < n → |a n| = (1/2 : ℚ) *
      ∑ _j ∈ Finset.range (n+1), (permutationCount (2*n-1) (n+1) : ℚ)) := by
  sorry

end OMA.S_oeis_a085799
