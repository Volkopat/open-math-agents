import Mathlib

/-!
# A124867: Numbers that are the sum of 3 distinct primes.

Source: https://oeis.org/A124867
Credit: @eltociear

The source states, in its COMMENTS section:
  (Conjecture) Every number n > 17 is the sum of 3 distinct primes. Natural numbers that
  are not the sum of 3 distinct primes are listed in A124868.

The sequence itself (A124867) is the increasing list of those representable numbers, and the
source's DATA line starts it at 10 = 2 + 3 + 5, the smallest sum of three distinct primes; the
EXAMPLE section then records that 13 = 3 + 3 + 7 = 3 + 5 + 5 only has representations with a
repeated prime, so 13 is not a term. The conjecture is exactly that the representable numbers
are 10, 12, 14, 15, 16 together with every integer above 17: the missing ones below 18 are
1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13 and 17, as in A124868.

Readings used below. A number is a sum of 3 distinct primes when there are primes p, q, r with
p < q < r and p + q + r = n; ordering the three summands this way is the same condition and is
the way distinctness is expressed without a separate pairwise-inequality hypothesis. The bound
is 17 < n, as in the source (number n > 17); nothing is said about n <= 17, of which some are
representable (10, 12, 14, 15, 16) and some are not.

Check that the statement is not trivially false: a sieve up to 6000 confirms that every integer
n with 17 < n <= 6000 is a sum of three distinct primes, and that the representable n <= 17 are
exactly 10, 12, 14, 15, 16, matching the source's DATA and the complement A124868.
-/

namespace OMA.S_oeis_a124867

theorem main : ∀ n : ℕ, 17 < n → ∃ p q r : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p < q ∧ q < r ∧ p + q + r = n := by
  sorry

end OMA.S_oeis_a124867
-- ci: re-run check-proof
