import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace OMA.S_oeis_a103176

open scoped ArithmeticFunction.sigma

/-- Conjecture (OEIS A103176): if `n ≥ 1` satisfies `prime(σ(n)) - prime(φ(n)) = 6`
(with 1-indexed primes, so `prime(k) = Nat.nth Nat.Prime (k - 1)`), then
`σ(n) - φ(n) = 2` and `n` is prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    Nat.nth Nat.Prime (σ 1 n - 1) - Nat.nth Nat.Prime (Nat.totient n - 1) = 6 →
    σ 1 n - Nat.totient n = 2 ∧ n.Prime := by
  sorry

end OMA.S_oeis_a103176
