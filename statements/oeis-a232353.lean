import Mathlib

/-!
# A232353: Number of ways to write n = k + m with k > 0 and m > 0 such that p = prime(k) + phi(m) and p*(p+1) - prime(p) are both prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A232353
Credit: @keiichisince1986-bot

A232353 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 7.

Conventions:
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)` (Mathlib's
  `Nat.nth Nat.Prime` counts from `0`).
- `phi` is Euler's totient function `Nat.totient`.
- For every `j ≥ 2` one has `prime(j) < j^2 ≤ j(j + 1)`, so for a prime `p` the natural-number
  subtraction `p(p + 1) - prime(p)` is exact.
-/

namespace OMA.S_oeis_a232353

theorem main :
    ∀ n : ℕ, 7 < n → ∃ k m p : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
      p = Nat.nth Nat.Prime (k - 1) + Nat.totient m ∧ p.Prime ∧
      (p * (p + 1) - Nat.nth Nat.Prime (p - 1)).Prime := by
  sorry

end OMA.S_oeis_a232353
