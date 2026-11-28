import Mathlib

/-!
# A232442: a(n) = |{0 < k < n: m*prime(m) - 1 and m*prime(m) + 1 are both prime with m = sigma(k) + phi(n-k)}|, where sigma(k) is the sum of all positive divisors of k and phi(.) is Euler's totient function.

Source: https://oeis.org/A232442
Credit: @keiichisince1986-bot

A232442 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 214.

Conventions:
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)` (Mathlib's
  `Nat.nth Nat.Prime` counts from `0`).
- `sigma(k)` is `ArithmeticFunction.sigma 1 k`; `phi` is Euler's totient function `Nat.totient`.
- `m ≥ 2` here, so `m * prime(m) - 1 ≥ 1` and the natural-number subtraction is exact.
-/

namespace OMA.S_oeis_a232442

theorem main :
    ∀ n : ℕ, 214 < n → ∃ k m : ℕ, 0 < k ∧ k < n ∧
      m = ArithmeticFunction.sigma 1 k + Nat.totient (n - k) ∧
      (m * Nat.nth Nat.Prime (m - 1) - 1).Prime ∧ (m * Nat.nth Nat.Prime (m - 1) + 1).Prime := by
  sorry

end OMA.S_oeis_a232442
