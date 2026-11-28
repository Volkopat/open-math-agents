import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A gcd identity for the sum of unitary prime divisors

A prime is a unitary divisor of n precisely when its exponent is one.
This is Yanev's identity in additive form, which preserves ordinary integer
subtraction without relying on truncated subtraction on natural numbers.

Source: https://oeis.org/A063956
Credit: @DomTheDeveloper
-/

namespace OMA.S_oeis_a063956

/-- Sum the primes whose exponent in n is exactly one. -/
def a (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, if n.factorization p = 1 then p else 0

/-- Multiplication of inputs and the two gcd correction terms. -/
theorem main :
    ∀ m n : ℕ, 0 < m → 0 < n →
      a (m * n) + a ((n ^ 2).gcd m) + a (n.gcd (m ^ 2)) = a n + a m := by
  sorry

end OMA.S_oeis_a063956
