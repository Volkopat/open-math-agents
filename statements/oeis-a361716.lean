import Mathlib

/-!
# A361716: a(n) = Sum_{k = 0..n-1} (-1)^k * binomial(n, k)^2 * binomial(n - 1, k)

Source: https://oeis.org/A361716
Credit: @ceejcake

OEIS A361716 (offset 0) is defined by
`a(n) = ∑_{k = 0}^{n - 1} (-1)^k * C(n, k)^2 * C(n - 1, k)`,
with initial values `a(0)..a(7) = 0, 1, -3, -8, 45, 126, -840, -2400`.
At `n = 0`, `Finset.range 0` is empty so `a 0 = 0`, matching OEIS offset 0.
For `n ≥ 1`, `k ∈ Finset.range n` ranges over `0 ≤ k ≤ n - 1`.

Conjecture (Peter Bala, OEIS A361716):
For all primes `p ≥ 5` and positive integers `n` and `k`,
`a(n * p^k) ≡ a(n * p^(k - 1)) (mod p^(3 * k))`.
Since `0 < k`, natural-number subtraction `k - 1` is exact.
-/

namespace OMA.S_oeis_a361716

/-- The integer sequence OEIS A361716:
`a(n) = ∑_{k = 0}^{n - 1} (-1)^k * C(n, k)^2 * C(n - 1, k)` for `n ≥ 0`
(with `a(0) = 0` as the empty sum). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2 * ((n - 1).choose k : ℤ)

/-- Supercongruence conjecture for OEIS A361716:
for all primes `p ≥ 5` and positive integers `n` and `k`,
`a(n * p^k) ≡ a(n * p^(k - 1)) (mod p^(3 * k))`. -/
theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry

end OMA.S_oeis_a361716
