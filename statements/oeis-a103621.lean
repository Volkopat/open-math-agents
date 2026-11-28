import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The trajectory of 7 under the sloping binary map

Chai Wah Wu proposed a recurrence and a rational ordinary generating function for
OEIS A103621. The sequence begins at index 1. Its constant coefficient is zero.

Sources: https://oeis.org/A103621 and https://oeis.org/A102370
Credit: @wtho704
-/

namespace OMA.S_oeis_a103621

/-- Sloane's formula for the sloping binary map A102370. The sum includes the
positive k such that 2^k divides n+k. For k > log₂(n)+1, one has 0 < n+k < 2^k. -/
def sloping (n : ℕ) : ℕ :=
  n + ∑ i ∈ Finset.range (n.log2 + 1),
    if (n + (i + 1)) % 2 ^ (i + 1) = 0 then 2 ^ (i + 1) else 0

/-- The orbit, with its initial value at time zero. -/
def orbit : ℕ → ℕ
  | 0 => 7
  | j + 1 => sloping (orbit j)

/-- The OEIS indexing, extended by a zero constant coefficient. -/
def a : ℕ → ℕ
  | 0 => 0
  | j + 1 => orbit j

/-- Coefficients of the proposed numerator in ascending degree. -/
def numerator : ℕ → ℕ
  | 1 => 7
  | 2 | 3 | 4 | 6 | 7 => 2
  | 5 => 10
  | 8 => 34
  | 9 => 3
  | _ => 0

/-- Wu's recurrence and the coefficient identity obtained by multiplying the
proposed generating function by 1 - x - x^8 + x^9. Truncated indices below zero
contribute zero because a(0) = 0. -/
theorem main :
    (∀ n : ℕ, 9 < n → a n + a (n - 9) = a (n - 1) + a (n - 8)) ∧
    (∀ n : ℕ, a n + a (n - 9) = numerator n + a (n - 1) + a (n - 8)) := by
  sorry

end OMA.S_oeis_a103621
