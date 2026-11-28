import Mathlib

/-!
# A394410: Quadratic recurrence a(1) = 1, a(2) = 3, a(n) = (a(n-1)^2 + a(n-2)^2) / 2

Source: https://oeis.org/A394410

Conjecture (Thomas Ordowski, via A056826):
If `a(n)` is prime, then `(a(n)^a(n) + 1) / (a(n) + 1)` is also prime.

Conventions:
- Offset: `1`, with `a 1 = 1`, `a 2 = 3`, `a 3 = 5`, `a 4 = 17`, `a 5 = 157`, `a 6 = 12469`, ...
- We set `a 0 = 0` as a dummy value and restrict the statement to `1 ≤ n`.
- Since all terms `a n` (for `n ≥ 1`) are odd, the integer divisions by `2` and by `a n + 1`
  are exact.
-/

namespace OMA.S_oeis_a394410

/-- The sequence A394410: `a 1 = 1`, `a 2 = 3`, and `a (n + 3) = (a (n + 2)^2 + a (n + 1)^2) / 2`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | n + 3 => (a (n + 2) ^ 2 + a (n + 1) ^ 2) / 2

/-- Conjecture (Thomas Ordowski): whenever `a n` is prime (for `n ≥ 1`),
`(a n ^ a n + 1) / (a n + 1)` is also prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → Nat.Prime (a n) →
      Nat.Prime ((a n ^ a n + 1) / (a n + 1)) := by
  sorry

end OMA.S_oeis_a394410
