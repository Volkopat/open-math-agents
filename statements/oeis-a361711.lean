import Mathlib

/-!
# A361711: a(1) = 1 and a(n) = Sum_{k = 0..n-2} (-1)^k * binomial(n, k)^2 * binomial(n - 2, k) for n >= 2

Source: https://oeis.org/A361711
Credit: @ceejcake

OEIS A361711 (offset 1) is defined by `a(1) = 1` and
`a(n) = ∑_{k = 0}^{n - 2} (-1)^k * C(n, k)^2 * C(n - 2, k)` for `n ≥ 2`,
with initial values `a(1)..a(8) = 1, 1, -8, 5, 126, -168, -2400, 4125`.
For `n ≥ 2`, `k ∈ Finset.range (n - 1)` ranges over `0 ≤ k ≤ n - 2`.

Conjecture (Peter Bala, OEIS A361711):
For all primes `p ≥ 5` and positive integers `k`,
`a(p^k) ≡ a(p^(k - 1)) (mod p^(3 * k))`.
Since `0 < k`, natural-number subtraction `k - 1` is exact (and `p^(k - 1) ≥ 1`,
using `a(1) = 1` when `k = 1`).
-/

namespace OMA.S_oeis_a361711

/-- The integer sequence OEIS A361711 (offset 1):
`a(1) = 1`, and `a(n) = ∑_{k = 0}^{n - 2} (-1)^k * C(n, k)^2 * C(n - 2, k)` for `n ≥ 2`. -/
def a (n : ℕ) : ℤ :=
  if n = 1 then 1
  else ∑ k ∈ Finset.range (n - 1),
    (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2 * ((n - 2).choose k : ℤ)

/-- Supercongruence conjecture for OEIS A361711:
for all primes `p ≥ 5` and positive integers `k`,
`a(p^k) ≡ a(p^(k - 1)) (mod p^(3 * k))`. -/
theorem main :
    ∀ p k : ℕ, p.Prime → 5 ≤ p → 0 < k →
      a (p ^ k) ≡ a (p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry

end OMA.S_oeis_a361711
