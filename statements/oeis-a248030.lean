import Mathlib

/-!
# A248030: Least positive integer m such that m + n divides sigma(m)*phi(n), where sigma(.) and phi(.) are given by A000203 and A000010.

Source: https://oeis.org/A248030
Credit: @eltociear

`a(n)` (offset 1) is the least `m > 0` such that `m + n` divides `σ(m) φ(n)` (`a(1) = 2`,
`a(2) = 12`). The entry conjectures (Zhi-Wei Sun):

  a(n) < 2n for any n > 2.

`main` states that for every `n > 2` some `m` with `0 < m < 2n` works; this is equivalent to the
least such `m` existing and being `< 2n`. `σ` is `ArithmeticFunction.sigma 1` (sum of divisors)
and `φ` is `Nat.totient`.
-/

namespace OMA.S_oeis_a248030

/-- The conjecture in OEIS A248030: for every `n > 2` there is `m` with `0 < m < 2n` and
`m + n ∣ σ(m) φ(n)`. -/
theorem main : ∀ n : ℕ, 2 < n →
    ∃ m : ℕ, 0 < m ∧ m < 2 * n ∧ m + n ∣ ArithmeticFunction.sigma 1 m * Nat.totient n := by
  sorry

end OMA.S_oeis_a248030
