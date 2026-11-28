import Mathlib

/-!
# A367865: a(n) = Sum_{d|n} d * phi(d) * mu(d)^2.

Source: https://oeis.org/A367865 (conjecture of Velin Yanev, Sep 14 2025).
Credit: @esracummings31-blip

Conjecture: a(n) = (rad(n)/n) * Sum_{k=1..n} rad(n*k)/rad(k), where rad is A007947 (the
product of the distinct primes dividing its argument). The right-hand side is computed in `ℚ`.
-/

namespace OMA.S_oeis_a367865

open scoped ArithmeticFunction.Moebius

/-- A367865. -/
def a (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (d : ℤ) * (d.totient : ℤ) * μ d ^ 2

/-- The squarefree kernel A007947. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem main :
    ∀ n, 1 ≤ n → (a n : ℚ) =
      (rad n : ℚ) / n * ∑ k ∈ Finset.Icc 1 n, (rad (n * k) : ℚ) / (rad k : ℚ) := by
  sorry

end OMA.S_oeis_a367865
