import Mathlib

/-!
# A124868: Natural numbers that are not the sum of 3 distinct primes.

Source: https://oeis.org/A124868
Credit: @azmiozgen

Conjecture (from the entry): every number n > 17 is the sum of 3 distinct primes, so the sequence is exactly 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 17.

Formalization notes:
* Stated as equality of the set of positive integers that are not a sum of three distinct primes with the listed twelve values.
* Controls (computed): the n < 3000 that are not such sums are exactly the twelve listed values.
-/

namespace OMA.S_oeis_a124868



/-- The conjecture of the entry. -/
theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ p + q + r = n} =
      ({1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 17} : Set ℕ) := by
  sorry

end OMA.S_oeis_a124868
