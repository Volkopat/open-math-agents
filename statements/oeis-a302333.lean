import Mathlib

/-!
# A302333: Wagstaff primes related to The New Mersenne Conjecture that are the indices of perfect numbers in a list of centered 9-gonal numbers.

Source: https://oeis.org/A302333
Credit: @agchua

The entry is by Steve Homewood, Apr 05 2018 (offset 1; data 3, 11, 43, 2731, 43691, 174763,
715827883, ...). Its comment line, verbatim:
  Let p be a Wagstaff prime related to The New Mersenne Conjecture. Then (3p-2)(3p-1)/2 gives
  the perfect number whose index it is.
Example of the entry: for p = 3, (3*3-2)*(3*3-1)/2 = 28 and for p = 11, (3*11-2)(3*11-1)/2 = 496.

Formalisation. A Wagstaff prime is a prime p = (2^q + 1)/3, that is 3*p = 2^q + 1. The listed
terms are the Wagstaff primes for q = 3, 5, 7, 13, 17, 19, 31, 61, 127, exactly the exponents
for which 2^q - 1 is a Mersenne prime as well; so p is related to The New Mersenne Conjecture
when 3*p = 2^q + 1 with p and 2^q - 1 both prime. The third condition of that conjecture
(q = 2^k + 1 or 2^k - 1 or 4^k + 3 or 4^k - 3) is not assumed, which only makes the claim
stronger. The list of centered 9-gonal numbers is A060544 (offset 1), with the formula
a(n) = (3*n-1)*(3*n-2)/2 of that entry. The claim is that the term with index p of this list is
(3p-2)(3p-1)/2 and that this number is perfect (Nat.Perfect: the sum of its proper divisors
equals it).
-/

namespace OMA.S_oeis_a302333

/-- A060544: centered 9-gonal numbers, a(n) = (3*n-1)*(3*n-2)/2. -/
def c9 (n : ℕ) : ℕ := (3 * n - 1) * (3 * n - 2) / 2

/-- If p is prime, 3*p = 2^q + 1 and 2^q - 1 is prime, then (3p-2)(3p-1)/2 is the centered
9-gonal number with index p and it is a perfect number. -/
theorem main :
    ∀ p q : ℕ, Nat.Prime p → 3 * p = 2 ^ q + 1 → Nat.Prime (2 ^ q - 1) →
      c9 p = (3 * p - 2) * (3 * p - 1) / 2 ∧ Nat.Perfect ((3 * p - 2) * (3 * p - 1) / 2) := by
  sorry

end OMA.S_oeis_a302333
