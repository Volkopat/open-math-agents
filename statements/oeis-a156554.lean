import Mathlib

/-!
# A156554: integer sequences of length 2n+1 with sum 0 and sum of absolute values 2n

Source: https://oeis.org/A156554

`a(n) = S(2n, n)`, the coordination sequence of the lattice `A_{2n}` at radius `n`, offset 0.
Peter Bala (Dec 19 2020) gives `a(n) = Sum_{k = 0..n} C(2n, n-k)^2 * C(2n+k-1, k)`, and conjectures:
for any prime `p >= 5`, `a(n*p^k) == a(n*p^(k-1)) (mod p^(3k))` for all positive integers `n` and `k`.
This file states that conjecture (the more general variants for other sequences are not stated).

Formalized: `a(n)` is an integer, defined by Bala's binomial sum with `Nat.choose`. The truncated
subtraction `2n+k-1` only truncates at `n = k = 0`, where `C(0, 0) = 1 = C(-1, 0)`, so the value
`a(0) = 1` is correct; for `n >= 1` no truncation happens. The congruence is divisibility of the
difference by `p^(3k)` in `ℤ`.
-/

namespace OMA.S_oeis_a156554

/-- A156554: `a(n) = Sum_{k = 0..n} C(2n, n-k)^2 * C(2n+k-1, k)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    ((Nat.choose (2 * n) (n - k) : ℤ) ^ 2 * (Nat.choose (2 * n + k - 1) k : ℤ))

/-- Bala's conjectured supercongruences: for primes `p >= 5` and `n, k >= 1`,
`a(n p^k) == a(n p^(k-1)) (mod p^(3k))`. -/
theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    ((p : ℤ) ^ (3 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a156554
