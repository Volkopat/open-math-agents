import Mathlib

namespace OMA.S_oeis_a127068

/-- Recurrence from OEIS A127068:
`d(m, 0) = 1`, `d(m, 1) = m`, and
`d(m, k) = (m - k + 1) * d(m + 1, k - 1) - (k - 1) * (m + 1) * d(m + 2, k - 2)` for `k ≥ 2`. -/
def dSeq (m : ℕ) : ℕ → ℤ
  | 0 => 1
  | 1 => (m : ℤ)
  | k + 2 =>
      ((m : ℤ) - (k + 1 : ℤ)) * dSeq (m + 1) (k + 1) -
        ((k + 1 : ℤ) * ((m + 1 : ℕ) : ℤ)) * dSeq (m + 2) k

/-- OEIS A127068: `a(n) = d(3, n)`. -/
def a127068 (n : ℕ) : ℤ :=
  dSeq 3 n

/-- Peter Bala's conjectures (OEIS A127068, Feb 15 2022):
1. For all `n : ℕ`, `a(2 * n) = (-1)^(n + 1) * (n + 1) * (2 * n - 1) * (2 * n)!`.
2. `a(1) = 3`, `a(3) = -30`, and for all `n ≥ 2`,
   `a(2 * n + 1) = -2 * (2 * n + 3) * (3 * n - 2) * a(2 * n - 1) - 4 * (n - 1) * (2 * n + 3) * (4 * n^2 - 1) * a(2 * n - 3)`. -/
theorem main :
    (∀ n : ℕ,
      a127068 (2 * n) =
        (-1 : ℤ) ^ (n + 1) * ((n + 1 : ℕ) : ℤ) * (2 * (n : ℤ) - 1) * (((2 * n).factorial : ℕ) : ℤ)) ∧
    a127068 1 = 3 ∧
    a127068 3 = -30 ∧
    (∀ n : ℕ, 2 ≤ n →
      a127068 (2 * n + 1) =
        -2 * (2 * (n : ℤ) + 3) * (3 * (n : ℤ) - 2) * a127068 (2 * n - 1) -
          4 * ((n : ℤ) - 1) * (2 * (n : ℤ) + 3) * (4 * (n : ℤ) ^ 2 - 1) * a127068 (2 * n - 3)) := by
  sorry

end OMA.S_oeis_a127068
