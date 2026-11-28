import Mathlib

namespace OMA.S_oeis_a112970

/-- A112970, a generalized Stern sequence: `a 0 = a 1 = 1`, `a (2n+1) = a n`,
`a (2n) = a n + a (n-2)` with `a m = 0` for negative `m`. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 1 then a ((n + 2) / 2)
    else a ((n + 2) / 2) + if 2 ≤ (n + 2) / 2 then a ((n + 2) / 2 - 2) else 0

/-- A033638: quarter-squares plus 1, `floor(n^2/4) + 1`. -/
def a033638 (n : ℕ) : ℕ := n ^ 2 / 4 + 1

/-- Conjectures (OEIS A112970): a(2^n) = a(2^(n+1)+1) = A033638(n) and
a(2^n - 1) = a(3*2^n - 1) = 1. -/
theorem main : ∀ n : ℕ, a (2 ^ n) = a033638 n ∧ a (2 ^ (n + 1) + 1) = a033638 n ∧
    a (2 ^ n - 1) = 1 ∧ a (3 * 2 ^ n - 1) = 1 := by
  sorry

end OMA.S_oeis_a112970
