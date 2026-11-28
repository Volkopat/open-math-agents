import Mathlib

/-!
# A248588: Least positive integer m such that m + n divides sigma(m), where sigma(m) is the sum of all positive divisors of m.

Source: https://oeis.org/A248588
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) exists for any n > 0.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m.
* pi = `Nat.primeCounting` (number of primes ≤ x).
* sigma = `ArithmeticFunction.sigma 1`, phi = `Nat.totient`, prime(k) = `Nat.nth Nat.Prime (k - 1)`.
* Controls (computed least m): a(1..9) = 2, 12, 4, 9, 40, 6, 8, 10, 15, as in the entry.
-/

namespace OMA.S_oeis_a248588

open ArithmeticFunction



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ sigma 1 m := by
  sorry

end OMA.S_oeis_a248588
