import Mathlib

/-!
# A276711: Number of primes p <= n such that n - p is a perfect power (including 0 and 1).

Source: https://oeis.org/A276711
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A276711 (Zhi-Wei Sun, Sep 15 2016):
For n > 1, we have a(n) > 0 except for n = 11^6 = 1771561. In other words, any integer n > 1
other than 11^6 can be written as p + x^k, where p is a prime, x is a nonnegative integer and
k is an integer greater than one.

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, ...). `a n` is the number
  of primes p such that n = p + x^k for some natural number x >= 0 and some integer k >= 2;
  this is the notion of perfect power including 0 and 1 used in the entry, and it forces
  p <= n.
* The statement is the positivity claim for every n > 1 with n ≠ 11^6. That a(11^6) = 0 is a
  finite computation and is not part of the statement.
* Only the first assertion is formalized; the further claim with x, k > 1 and the exceptions
  8, 24, 1549, 1771561 is a separate conjecture.
-/

namespace OMA.S_oeis_a276711

/-- A276711: number of primes p with n = p + x^k for some x >= 0 and k >= 2. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ | p.Prime ∧ ∃ x k : ℕ, 2 ≤ k ∧ p + x ^ k = n}

/-- The conjecture of Sun: a(n) > 0 for every n > 1 other than 11^6. -/
theorem main : ∀ n : ℕ, 1 < n → n ≠ 11 ^ 6 → 0 < a n := by
  sorry

end OMA.S_oeis_a276711
