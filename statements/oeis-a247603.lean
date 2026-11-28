import Mathlib

/-!
# A247603: Least integer m > 0 with pi(m*n) = sigma(m), where sigma(m) is the sum of all positive divisors of m.

Source: https://oeis.org/A247603
Credit: @eltociear

`a(n)` (offset 2) is the least `m > 0` with `π(m n) = σ(m)` (`a(2) = 1`, `a(4) = 23`). The entry
conjectures (Zhi-Wei Sun):

  a(n) exists for any n > 1.

`main` states that for every `n ≥ 2` some `m > 0` has `π(m n) = σ(m)`. `π(x)` is `Nat.primeCounting x`, the number of primes `≤ x`. `σ` is `ArithmeticFunction.sigma 1` (sum of divisors) and `φ` is `Nat.totient`.
-/

namespace OMA.S_oeis_a247603


/-- The conjecture in OEIS A247603: for every `n ≥ 2` there is `m > 0` with `π(m n) = σ(m)`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ m : ℕ, 0 < m ∧ Nat.primeCounting (m * n) = ArithmeticFunction.sigma 1 m := by
  sorry

end OMA.S_oeis_a247603
