import Mathlib

/-!
# A276825: Number of ways to write n as x^3 + P_2, where x and P_2 are positive integers with P_2 a product of at most two primes.

Source: https://oeis.org/A276825
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry; verified for n up to 10^8): any integer n > 1 can be written as
x^3 + P_2, where x and P_2 are positive integers with P_2 a product of at most two primes. (The further
guesses in the entry are not stated here.)

Formalization notes:
* "A product of at most two primes" includes 1 (the empty product), the primes and the semiprimes:
  a positive integer whose prime factors, with multiplicity, number at most two.
* Controls (computed): every n with 1 < n < 20000 has such a representation; a(2) = 1 via 2 = 1 + 1.
-/

namespace OMA.S_oeis_a276825



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 1 < n → ∃ x P : ℕ, 0 < x ∧ 0 < P ∧ P.primeFactorsList.length ≤ 2 ∧ x ^ 3 + P = n := by
  sorry

end OMA.S_oeis_a276825
