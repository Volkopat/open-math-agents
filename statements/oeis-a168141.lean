import Mathlib

/-!
# A168141: a(n) = pi(n + 1) - pi(n - 2), where pi is the prime counting function.

Source: https://oeis.org/A168141
Credit: @prasledi

Conjecture (Andrew Slattery, Apr 26 2020, in the COMMENTS of A168141): a(n) = 2 for infinitely
many n. (The comment adds that this is equivalent to the twin prime conjecture.)

Formalization notes:
* pi is Mathlib's `Nat.primeCounting` (pi(x) = number of primes <= x).
* The offset is 1. For n = 1, n - 2 is negative and pi(-1) = 0; the natural-number subtraction
  gives pi(0) = 0, the same value, and for n >= 2 it is the ordinary difference. So
  a(n) = pi(n+1) - pi(n-2) with natural-number subtraction (pi is monotone, so the outer
  subtraction is exact). This reproduces the OEIS data 1, 2, 2, 2, 1, 2, 1, 1, 0, ...
* Allowing n = 0 does not change whether the set is infinite.
-/

namespace OMA.S_oeis_a168141

/-- A168141: `a(n) = π(n + 1) - π(n - 2)`. -/
def a (n : ℕ) : ℕ := Nat.primeCounting (n + 1) - Nat.primeCounting (n - 2)

/-- Slattery's conjecture: `a(n) = 2` for infinitely many `n`. -/
theorem main : {n : ℕ | a n = 2}.Infinite := by
  sorry

end OMA.S_oeis_a168141
