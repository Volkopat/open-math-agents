import Mathlib

/-!
# A055008: Numbers k such that gcd(phi(k), sigma(k)) = 1.

Source: https://oeis.org/A055008
Credit: @bnb9001

Here phi is Euler's totient `Nat.totient` and sigma is the sum of divisors
`ArithmeticFunction.sigma 1`.

Conjecture (Jason Yuen, 2024): every term is a square or twice a square. Amiram Eldar notes
that the conjecture is true.
-/

namespace OMA.S_oeis_a055008

/-- Every `k` with `gcd(phi k, sigma k) = 1` is a square or twice a square. -/
theorem main : ∀ k : ℕ, Nat.gcd k.totient (ArithmeticFunction.sigma 1 k) = 1 →
    IsSquare k ∨ ∃ m, k = 2 * m ^ 2 := by
  sorry

end OMA.S_oeis_a055008
