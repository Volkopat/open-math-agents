import Mathlib

/-!
# OEIS A091699 — row sums of the inverse of an integer triangle

Christian G. Bower defined A091699 as the row sums of A091698, the inverse of
the lower triangular matrix A063967. R. J. Mathar proposed the recurrence in 2012.
Rows and columns start at zero.

Sources: https://oeis.org/A091699, https://oeis.org/A091698, https://oeis.org/A063967.
OEIS Foundation, CC BY-SA 4.0. Lean formalization: @rifter0418.
-/

namespace OMA.S_oeis_a091699

/-- Entry (n,k) of A063967, using its binomial formula. -/
def triangle (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (Nat.choose j (n - j) : ℤ) * (Nat.choose j k : ℤ)

/-- Entry (n,k) of A091698. Since the diagonal of A063967 is one, forward
substitution in the matrix equation A063967 · A091698 = I gives this formula. -/
def inverseEntry (n k : ℕ) : ℤ :=
  (if n = k then 1 else 0) - ∑ i : Fin n, triangle n i.val * inverseEntry i.val k
termination_by n
decreasing_by exact i.isLt

/-- The sum of row n of A091698. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), inverseEntry n k

/-- Mathar's recurrence, starting where all four sequence indices are defined. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      2 * (n : ℤ) * a n + (13 * (n : ℤ) - 16) * a (n - 1) +
        4 * (4 * (n : ℤ) - 7) * a (n - 2) + 5 * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a091699
