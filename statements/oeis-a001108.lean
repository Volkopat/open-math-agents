import Mathlib

/-!
# A001108: a(n)-th triangular number is a square

Source: https://oeis.org/A001108
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(0) = 0`, `a(1) = 1`, `a(n+1) = 6 a(n) - a(n-1) + 2` (so `0, 1, 8, 49, 288, …`).
Conjecture (OEIS comment): the terms are also the numbers `n` such that `σ(n)` and
`σ(n(n+1)/2)` (sigma of the `n`-th triangular number) are both odd.

## Encoding

* `σ` is `ArithmeticFunction.sigma 1`.
* The comment is about positive `n` (the sequence's term `a(0) = 0` is not a meaningful input
  for `σ`), so `main` says: for `n > 0`, both values are odd iff `n = a(k)` for some `k ≥ 1`.
* The other conjecture in the same OEIS entry (about A123737) is not stated here.
-/

namespace OMA.S_oeis_a001108

open ArithmeticFunction

/-- `a(n)`: `0, 1, 8, 49, 288, …` -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 6 * a (n + 1) - a n + 2

theorem main :
    ∀ n : ℕ, 0 < n →
      (Odd (sigma 1 n) ∧ Odd (sigma 1 (n * (n + 1) / 2)) ↔ ∃ k : ℕ, 1 ≤ k ∧ a k = n) := by
  sorry

end OMA.S_oeis_a001108
