import Mathlib

/-!
# A230022: a(n) = |{the number of primes in the interval (k*n, (k+1)*n]: k = 0, 1, ..., n-1}|.

Source: https://oeis.org/A230022
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) is at least sqrt(n-1) for each n > 0, and equality holds only when n is 2 or 26.
(ii) The sequence contains all positive integers.

Formalization notes:
* a(n) is the number of distinct values among pi((k+1)n) - pi(kn), k = 0..n-1, with
  pi = `Nat.primeCounting`.
* Since a(n) ≥ 0, "a(n) ≥ sqrt(n-1)" is a(n)^2 ≥ n - 1 and equality is a(n)^2 = n - 1.
* (ii) is stated as: every m ≥ 1 equals a(n) for some n ≥ 1.
* Controls (computed): a(1..25) = 1, 1, 2, 2, 3, 3, 3, 4, 3, 4, 5, 5, 4, 5, 4, 5, 5, 6, 7, 6, 5, 6, 6,
  6, 5, as in the entry; for n < 300, (i) holds with equality only at n = 2, 26, and the values
  include 1, ..., 12.
-/

namespace OMA.S_oeis_a230022

/-- A230022(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n).image fun k => Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n)).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → n - 1 ≤ a n ^ 2 ∧ (a n ^ 2 = n - 1 ↔ n = 2 ∨ n = 26)) ∧
      ∀ m : ℕ, 0 < m → ∃ n, 0 < n ∧ a n = m := by
  sorry

end OMA.S_oeis_a230022
