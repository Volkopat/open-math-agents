import Mathlib

/-!
# A133802: Even numbers which are not the sum of a pair of cousin primes.

Source: https://oeis.org/A133802
Credit: @darealpandaboi

Conjecture: the sequence is complete (no other n < 10^9).

Translation notes.
* A cousin prime is a prime p with p - 4 or p + 4 prime (A023200 together with A046132). An even
  n is a term when it is not p + q with p, q cousin primes (p = q allowed: 6 = 3 + 3).
  This reading reproduces all 37 listed terms 2, 4, 8, 12, 68, ..., 2948, 2952 and finds no other
  even term up to 10000 (checked by computer).
* Complete is stated as: the set of such positive even numbers is exactly the set of listed terms.
-/

namespace OMA.S_oeis_a133802

/-- p is a cousin prime: p is prime and p - 4 or p + 4 is prime. -/
def IsCousinPrime (p : ℕ) : Prop := p.Prime ∧ ((p + 4).Prime ∨ (4 < p ∧ (p - 4).Prime))

theorem main :
    {n : ℕ | 0 < n ∧ Even n ∧ ¬ ∃ p q : ℕ, IsCousinPrime p ∧ IsCousinPrime q ∧ n = p + q} =
      {2, 4, 8, 12, 68, 72, 76, 278, 282, 286, 638, 642, 644, 648, 652, 908, 912, 916, 1058,
        1062, 1066, 1328, 1332, 1336, 1418, 1422, 2114, 2118, 2122, 2294, 2298, 2302, 2528, 2532,
        2536, 2948, 2952} := by
  sorry

end OMA.S_oeis_a133802
