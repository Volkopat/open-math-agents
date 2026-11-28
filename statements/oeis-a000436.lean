import Mathlib

/-!
# OEIS A000436

Generalized Euler numbers `c(3, n)`, with exponential generating function
`cos(x) / cos(3 * x) = 1 / (2 * cos(2 * x) - 1) = Sum_{n >= 0} a(n) * x^(2 * n) / (2 * n)!`.

Equivalently, `a(0) = 1` and for `n >= 1`:
`a(n) = 2 * Sum_{k = 0..n-1} (-1)^(n - k - 1) * binomial(2 * n, 2 * k) * 4^(n - k) * a(k)`.
(First terms: `1, 8, 352, 38528, 7869952, 2583554048, ...`)

Conjecture:
For each positive integer `k`, the sequence `a(n) (mod k)` is eventually periodic with
period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a000436

/-- Generalized Euler numbers `c(3, n)` (OEIS A000436), defined by the recurrence from
`(2 * cos(2 * x) - 1) * Sum_{n >= 0} a(n) * x^(2 * n) / (2 * n)! = 1`. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
    2 * ∑ k : Fin (n + 1),
      (-1 : ℤ) ^ (n - k.1) * (Nat.choose (2 * (n + 1)) (2 * k.1) : ℤ) * 4 ^ (n + 1 - k.1) * a k.1
termination_by n => n

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [ZMOD k] := by
  sorry

end OMA.S_oeis_a000436
