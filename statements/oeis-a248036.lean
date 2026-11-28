import Mathlib

/-!
# A248036: Least positive integer m such that m + n divides sigma(m)^2 + sigma(n)^2, where sigma(k) denotes the number of positive divisors of k.

Source: https://oeis.org/A248036
Credit: @eltociear

`a(n)` (offset 1) is the least `m > 0` such that `m + n` divides `σ(m)^2 + σ(n)^2`. The entry
conjectures (Zhi-Wei Sun):

  a(n) exists for any n > 0.

`main` states that for every `n ≥ 1` some `m > 0` works.

Note for reviewers: the entry's name glosses `sigma(k)` as "the number of positive divisors of
k", but its data (`1, 3, 2, 1, 10, 6, 3, 50, 1, 5, ...`) is reproduced by `σ` = sum of divisors
(`ArithmeticFunction.sigma 1`, A000203), and not by the divisor-count function (which would give
`a(2) = 2`, `a(3) = 5`). `main` follows the data and uses the sum of divisors.
-/

namespace OMA.S_oeis_a248036


/-- The conjecture in OEIS A248036: for every `n ≥ 1` there is `m > 0` with
`m + n ∣ σ(m)^2 + σ(n)^2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧
    m + n ∣ ArithmeticFunction.sigma 1 m ^ 2 + ArithmeticFunction.sigma 1 n ^ 2 := by
  sorry

end OMA.S_oeis_a248036
