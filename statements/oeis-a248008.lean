import Mathlib

/-!
# A248008: Least positive integer m such that m + n divides sigma(m*n), where sigma(k) denotes the sum of all positive divisors of k.

Source: https://oeis.org/A248008
Credit: @eltociear

`a(n)` (offset 1) is the least `m > 0` such that `m + n` divides `σ(m n)` (`a(1) = 2`: `3 ∣ σ(2)`).
The entry conjectures (Zhi-Wei Sun):

  a(n) exists for any n > 0.

`main` states that for every `n ≥ 1` some `m > 0` works. `σ` is `ArithmeticFunction.sigma 1`.
-/

namespace OMA.S_oeis_a248008


/-- The conjecture in OEIS A248008: for every `n ≥ 1` there is `m > 0` with `m + n ∣ σ(m n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ m + n ∣ ArithmeticFunction.sigma 1 (m * n) := by
  sorry

end OMA.S_oeis_a248008
