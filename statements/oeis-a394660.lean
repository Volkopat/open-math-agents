import Mathlib

/-!
# A394660: a(n) is the largest prime number such that prime(n)-a(n) is a 3-smooth number where prime(n) denotes the n-th prime number, or zero if no such number exists.

Source: https://oeis.org/A394660
Credit: @luciusacarr

Data: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
97, 101, 103, 107, 109, 109, 127, ... (offset 2).

Conjecture (from the entry): no term is 0 (verified to n = 10^7). `main` states it.

Reading of the source:
* A 3-smooth number (A003586) is a positive integer of the form `2^a * 3^b` (1 included).
  Since 3-smooth numbers are positive, a(n) is a prime `q < prime(n)` (example: prime(31) = 127,
  127 - 113 = 14 is not 3-smooth, 127 - 109 = 18 = 2 * 3^2 is, so the term is 109).
* The offset is 2 (a(2) = 2 for prime(2) = 3), so `prime(n)` ranges over the odd primes.
* "No term is 0" is stated as: for every prime `p ≥ 3` there is a prime `q < p` such that
  `p - q` is 3-smooth (the largest such `q` then exists, being below `p`).
-/

namespace OMA.S_oeis_a394660

theorem main :
    -- No term is 0: every odd prime p has a prime q < p with p - q 3-smooth.
    ∀ p : ℕ, p.Prime → 3 ≤ p → ∃ q : ℕ, q.Prime ∧ q < p ∧ ∃ a b : ℕ, p - q = 2 ^ a * 3 ^ b := by
  sorry

end OMA.S_oeis_a394660
