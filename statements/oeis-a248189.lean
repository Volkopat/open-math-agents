import Mathlib

/-!
# A248189: Least positive integer m such that m*n divides sigma(m^2+n^2), where sigma(k) is the sum of all positive divisors of k.

Source: https://oeis.org/A248189
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) exists for any n > 0.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m.
* pi = `Nat.primeCounting` (number of primes ≤ x).
* sigma = `ArithmeticFunction.sigma 1`, phi = `Nat.totient`, prime(k) = `Nat.nth Nat.Prime (k - 1)`.
* Controls (computed least m): a(1..8) = 1, 1, 1, 7, 2, 38, 4, 81, as in the entry.
-/

namespace OMA.S_oeis_a248189

open ArithmeticFunction



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m * n ∣ sigma 1 (m ^ 2 + n ^ 2) := by
  sorry

end OMA.S_oeis_a248189
