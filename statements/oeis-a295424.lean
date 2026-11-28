import Mathlib

/-!
# A295424: a twin prime in a Goldbach partition

Source: https://oeis.org/A295424
Credit: @rodolfoquint

The conjecture concerns every even integer n > 4 (rather than the sequence
index, whose partitions sum to 2*n). A twin prime is either member of a pair
of primes differing by 2, as in the source's `istwin` predicate.

The Goldbach summands may coincide. Their twin partner need not be the other
summand: the entry's example counts 3, 5 and 7 among the partitions of 10.
By symmetry the summand belonging to a twin-prime pair is named p below.
-/

namespace OMA.S_oeis_a295424

theorem main :
    ∀ n : ℕ, Even n → 4 < n →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n ∧
        ∃ r : ℕ, r.Prime ∧ (r + 2 = p ∨ p + 2 = r) := by
  sorry

end OMA.S_oeis_a295424
