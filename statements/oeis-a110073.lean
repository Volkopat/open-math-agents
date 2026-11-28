import Mathlib

/-!
# OEIS A110073: form of the terms above 76

Source: https://oeis.org/A110073 (OEIS Foundation, CC BY-SA 4.0).
Credit: @kumagi

A110073 consists of positive integers satisfying `σ(n) = 2n − φ(φ(n))`,
where `σ` is the sum of the positive divisors and `φ` is Euler's totient.
The conjecture says that each term above 76 equals `80p + 10` for a prime
`p` such that `8p + 1` is prime. The defining equation uses integer subtraction.
-/

namespace OMA.S_oeis_a110073

theorem main : ∀ n : ℕ, 76 < n →
    (ArithmeticFunction.sigma 1 n : ℤ) = 2 * (n : ℤ) - (n.totient.totient : ℤ) →
    ∃ p : ℕ, p.Prime ∧ (8 * p + 1).Prime ∧ n = 80 * p + 10 := by
  sorry

end OMA.S_oeis_a110073
