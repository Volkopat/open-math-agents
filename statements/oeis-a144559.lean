import Mathlib

/-!
# A144559: a(n) = number of triples [i,j,k] with i+j+k = n, i an odd prime, j an odd Fibonacci number and k a positive Fibonacci number.

Source: https://oeis.org/A144559
Credit: @keiichisince1986-bot

A144559 is the sequence `a(n)` named in the title. The entry states:
Zhi-Wei Sun conjectured on the Number Theory Mailing List that a(n) > 0 for all n > 4. (The entry adds:
verified by D. S. McNeil for all n < 10^13.)

Conventions:
- Fibonacci numbers are the values `Nat.fib m` (`m ≥ 0`, `F(0) = 0`, `F(1) = 1`). An odd Fibonacci number
  is a value `Nat.fib a` that is odd; a positive Fibonacci number is a value `Nat.fib b > 0`.
- `a(n) > 0` means that `n = i + j + k` with `i` an odd prime, `j` an odd Fibonacci number and `k` a
  positive Fibonacci number.
-/

namespace OMA.S_oeis_a144559

theorem main :
    ∀ n : ℕ, 4 < n → ∃ p a b : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd (Nat.fib a) ∧ 0 < Nat.fib b ∧
      p + Nat.fib a + Nat.fib b = n := by
  sorry

end OMA.S_oeis_a144559
