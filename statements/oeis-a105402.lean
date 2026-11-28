import Mathlib

/-!
# A105402: Positive integers k such that the prime factors of sigma(k) are a subset of the prime factors of k.

Source: https://oeis.org/A105402
Credit: @gblacher2

Conjecture (comment section of A105402, Antti Karttunen, Nov 04 2026):
"Pomerance has conjectured that all terms are even after the initial 1, see page 6 of
"Prime-Perfect Numbers" paper."

The paper is P. Pollack and C. Pomerance, Prime-perfect numbers, Integers 12A (2012),
Art. A14. Its Conjecture 6 (page 6) reads "Each prime-perfect number n > 1 is even", where n
is prime-perfect when n and sigma(n) have the same set of distinct prime factors. The terms
of A105402 are the numbers the same paper calls prime-deficient (every prime dividing sigma(n)
divides n), a larger set. The statement below is the conjecture as the OEIS comment states it,
for every term of A105402; it implies Conjecture 6 of the paper.

The sequence has offset 1: 1, 6, 28, 30, 42, 66, 84, 102, 120, ...

Modelling choices:
* `sigma k` is the sum of the divisors of `k`, `ArithmeticFunction.sigma 1 k`.
* "The prime factors of sigma(k) are a subset of the prime factors of k" is
  `(sigma 1 k).primeFactors ⊆ k.primeFactors`, as in the PARI program of the entry (every
  prime factor of sigma(n) divides n). The sequence lists positive integers only, so `0 < k`
  is part of the definition.
* "All terms are even after the initial 1" is stated for every term `k ≠ 1`, which does not
  depend on how the terms are indexed.
-/

namespace OMA.S_oeis_a105402

open ArithmeticFunction

/-- `k` is a term of A105402: `k` is positive and every prime factor of `sigma(k)` is a prime
factor of `k`. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ (sigma 1 k).primeFactors ⊆ k.primeFactors

/-- Pomerance's conjecture, as stated in A105402: every term other than 1 is even. -/
theorem main : ∀ k : ℕ, IsTerm k → k ≠ 1 → Even k := by
  sorry

end OMA.S_oeis_a105402
