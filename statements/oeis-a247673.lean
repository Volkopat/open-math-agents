import Mathlib

/-!
# A247673: Least integer m > 0 with pi(m*n) = sigma(m) + sigma(n), where pi(.) and sigma(.) are given by A000720 and A000203 respectively.

Source: https://oeis.org/A247673
Credit: @eltociear

`a(n)` (offset 5) is the least `m > 0` with `π(m n) = σ(m) + σ(n)` (`a(5) = 23`, `a(6) = 47`). The
entry conjectures (Zhi-Wei Sun):

  a(n) exists for every n = 5, 6, ... .

`main` states that for every `n ≥ 5` some `m > 0` has `π(m n) = σ(m) + σ(n)`. `π(x)` is `Nat.primeCounting x`, the number of primes `≤ x`. `σ` is `ArithmeticFunction.sigma 1` (sum of divisors) and `φ` is `Nat.totient`.
-/

namespace OMA.S_oeis_a247673


/-- The conjecture in OEIS A247673: for every `n ≥ 5` there is `m > 0` with
`π(m n) = σ(m) + σ(n)`. -/
theorem main : ∀ n : ℕ, 5 ≤ n → ∃ m : ℕ, 0 < m ∧
    Nat.primeCounting (m * n) = ArithmeticFunction.sigma 1 m + ArithmeticFunction.sigma 1 n := by
  sorry

end OMA.S_oeis_a247673
