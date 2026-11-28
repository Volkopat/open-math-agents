import Mathlib

/-!
# A272170: Second most significant bit of Fibonacci numbers > 1 written in base 2.

Source: https://oeis.org/A272170
Credit: @avivorly

For n ≥ 3 (the entry's offset; F(n) ≥ 2), a(n) is the second most significant binary digit of the
Fibonacci number F(n): with k = ⌊log₂ F(n)⌋ ≥ 1, it is ⌊F(n) / 2^(k-1)⌋ mod 2 (the entry's examples:
F(3) = 2 = 10₂ gives 0, F(4) = 3 = 11₂ gives 1, F(7) = 13 = 1101₂ gives 1).

Conjecture in the entry (Andres Cicuttin, 2016): there are no more than two consecutive 0's or 1's
(tested up to n = 10^5), i.e. no three consecutive terms are equal.
-/

namespace OMA.S_oeis_a272170

/-- a(n): the second most significant binary digit of `Nat.fib n` (for `n ≥ 3`). -/
def a (n : ℕ) : ℕ :=
  (Nat.fib n / 2 ^ (Nat.log 2 (Nat.fib n) - 1)) % 2

theorem main : ∀ n : ℕ, 3 ≤ n → ¬ (a n = a (n + 1) ∧ a (n + 1) = a (n + 2)) := by
  sorry

end OMA.S_oeis_a272170
