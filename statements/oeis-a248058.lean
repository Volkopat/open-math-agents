import Mathlib

/-!
# A248058: Least positive integer m such that m*n divides phi(m^2+n^2), where phi(.) is Euler's totient function.

Source: https://oeis.org/A248058
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) exists for any n > 0.
(ii) For each n > 0, there is a positive integer m such that m*n divides sigma(m^2+n^2), where
sigma(k) is the sum of all positive divisors of k.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m.
* Controls (computed): a(1..12) = 1, 1, 2, 1, 4, 1, 8, 1, 10, 1, 726, 2, as in the entry.
-/

namespace OMA.S_oeis_a248058

open ArithmeticFunction

/-- Both parts of the conjecture. -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m * n ∣ Nat.totient (m ^ 2 + n ^ 2)) ∧
      ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m * n ∣ sigma 1 (m ^ 2 + n ^ 2) := by
  sorry

end OMA.S_oeis_a248058
