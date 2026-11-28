import Mathlib.Data.Int.Basic

/-!
# OEIS A051397

R. J. Mathar's recurrence of order two for the sequence defined by
`a(n) = (2n - 2)(2n - 1)a(n - 1) + 1`. The entry gives `a(0) = 0`
so the recurrence of order two starts at index two, where both preceding terms are defined.

Source: https://oeis.org/A051397
-/

namespace OMA.S_oeis_a051397

/-- The defining recurrence, written at the successor index. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => (2 * (n : ℤ)) * (2 * (n : ℤ) + 1) * a n + 1

theorem main : ∀ n : ℕ, 2 ≤ n →
    let m : ℤ := n
    a n + (-4 * m ^ 2 + 6 * m - 3) * a (n - 1) +
      2 * (2 * m - 3) * (m - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a051397
