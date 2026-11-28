import Mathlib

/-!
# A258044: Fibonacci numbers that can be expressed as the sum of 2 consecutive primes

Source: https://oeis.org/A258044

Conjecture (OEIS A258044):
There are only finitely many Fibonacci numbers that can be written as the sum of two
consecutive prime numbers.

Conventions:
- Offset: `1`; known terms: `5 = 2 + 3`, `8 = 3 + 5`, `144 = 71 + 73`.
- `Nat.nth Nat.Prime k` and `Nat.nth Nat.Prime (k + 1)` are the `(k + 1)`-th and `(k + 2)`-th
  prime numbers (0-indexed).
-/

namespace OMA.S_oeis_a258044

/-- The set of Fibonacci numbers equal to the sum of two consecutive primes (OEIS A258044). -/
def S : Set ℕ :=
  {m : ℕ | (∃ n : ℕ, m = Nat.fib n) ∧
    ∃ k : ℕ, m = Nat.nth Nat.Prime k + Nat.nth Nat.Prime (k + 1)}

/-- Conjecture: OEIS A258044 is finite. -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a258044
