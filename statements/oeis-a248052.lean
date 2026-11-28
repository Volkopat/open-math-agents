import Mathlib

/-!
# A248052: Least positive integer m such that m + n divides pi(m^2) + pi(n^2), where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A248052
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) exists for any n > 0.
(ii) For each integer m > 0, there is a positive integer n such that m + n divides
prime(m^2) + prime(n^2).

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m.
* pi = `Nat.primeCounting` (number of primes ≤ x).
* sigma = `ArithmeticFunction.sigma 1`, phi = `Nat.totient`, prime(k) = `Nat.nth Nat.Prime (k - 1)`.
* Controls (computed least m): a(1..9) = 1, 2, 1, 8, 7, 7, 5, 1, 25, as in the entry; (ii) holds for m < 40.
-/

namespace OMA.S_oeis_a248052

open ArithmeticFunction

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture of the entry. -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ Nat.primeCounting (m ^ 2) + Nat.primeCounting (n ^ 2)) ∧
      ∀ m : ℕ, 0 < m → ∃ n : ℕ, 0 < n ∧ m + n ∣ prime (m ^ 2) + prime (n ^ 2) := by
  sorry

end OMA.S_oeis_a248052
