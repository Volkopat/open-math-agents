import Mathlib

/-!
# A081320: Largest 3-smooth divisor of n-th Fibonacci number.

Source: https://oeis.org/A081320
Credit: @bnb9001

The largest 3-smooth divisor of a positive integer m is 2^(v_2(m)) * 3^(v_3(m)), where v_p is the
p-adic valuation (`Nat.factorization m p`). a(n) is this for m = F(n), the n-th Fibonacci number
(offset 1: 1, 1, 2, 3, 1, 8, 1, 3, 2, 1, 1, 144, ...).

Conjecture (first part): for n > 12 with n > 0 modulo 12 (n not a multiple of 12),
a(n) = a(n-12). Charles R Greathouse IV notes that the first part of the conjecture follows
from the fact that the Fibonacci numbers are a strong divisibility sequence. (The entry's
second clause, about a(12k), is a separate statement and is not formalized here.)
-/

namespace OMA.S_oeis_a081320

/-- The largest 3-smooth divisor of `m` (for `m ≠ 0`): `2^(v_2 m) * 3^(v_3 m)`. -/
def smooth3Part (m : ℕ) : ℕ := 2 ^ m.factorization 2 * 3 ^ m.factorization 3

/-- A081320: the largest 3-smooth divisor of `F(n)`. -/
def a (n : ℕ) : ℕ := smooth3Part (Nat.fib n)

/-- The first part of the conjecture, proved: `a(n) = a(n-12)` for `n > 12` not divisible by 12. -/
theorem main : ∀ n : ℕ, 12 < n → n % 12 ≠ 0 → a n = a (n - 12) := by
  sorry

end OMA.S_oeis_a081320
