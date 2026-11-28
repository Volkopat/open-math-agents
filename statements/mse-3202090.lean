import Mathlib

/-!
# The only solution of `p^n - p = q^m - q` in odd primes `p > q`

Source: https://math.stackexchange.com/questions/3202090

Consider numbers `p^n - p` with `p > 2` prime and `n > 1`. The number `2184 = 3⁷ - 3 = 13³ - 13`
has two such representations. Prove that this is the only solution of the Diophantine equation
`p^n - p = q^m - q` with `p` and `q` odd primes, `p > q` (and `n, m > 1`). (This would follow
from a conjecture of Bennett; no other solution is known below `10²⁴`.)

Formalization notes:
* The unknowns are natural numbers; `p^n ≥ p` and `q^m ≥ q`, so the subtractions are exact.
* The unique solution is `(p, n, q, m) = (13, 3, 3, 7)`.
-/

namespace OMA.S_mse_3202090

/-- If `p > q` are odd primes, `n, m > 1` and `p^n - p = q^m - q`, then `p = 13`, `n = 3`,
`q = 3`, `m = 7`. -/
theorem main : ∀ p q n m : ℕ, p.Prime → q.Prime → Odd p → Odd q → q < p → 1 < n → 1 < m →
    p ^ n - p = q ^ m - q → p = 13 ∧ n = 3 ∧ q = 3 ∧ m = 7 := by
  sorry

end OMA.S_mse_3202090
