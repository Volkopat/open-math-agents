import Mathlib

/-!
# OEIS A015849: phi(n + 9) | sigma(n), n not divisible by 3

Source: https://oeis.org/A015849
Credit: @unserus

OEIS (Robert Israel, Jan 10 2019): "Includes primes p such that (p+9)/8 is prime.
Thus Dickson's conjecture implies the sequence is infinite."

The terms are the `n ≥ 1` with `n` not congruent to 0 mod 3 and
`φ(n + 9) ∣ σ(n)`, where `φ` is Euler's totient and `σ` the sum of divisors
(`ArithmeticFunction.sigma 1`). The open statement is that the sequence is
infinite.
-/

namespace OMA.S_oeis_a015849

/-- The sum of divisors. -/
abbrev sigma (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- The terms of A015849. -/
def a015849Set : Set ℕ := {n | 1 ≤ n ∧ n % 3 ≠ 0 ∧ Nat.totient (n + 9) ∣ sigma n}

/-- A015849 is infinite. -/
theorem main : a015849Set.Infinite := by
  sorry

end OMA.S_oeis_a015849
