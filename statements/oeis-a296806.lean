import Mathlib

/-!
# A296806: Take a prime, convert it to base 2, remove its most significant digit and its least significant digit and convert it back to base 10. Sequence lists primes that generate another prime by this process.

Source: https://oeis.org/A296806
Credit: @agchua

Comment of A296806 (Paolo Iachia, Dec 21 2017), its last sentence, verbatim:
  Conjecture: for any positive integer p, there are infinitely many primes q for which there
  exists an integer n such that q-(2p+1) = 2^n.

Formalisation. The earlier sentences of the same comment define the core
C(q) = (q - 2^floor(log_2(q)) - 1)/2 of a prime q, give examples and elementary remarks, and ask
whether there are more cases in which q and C(q) are both Mersenne primes; that question is not
a claim. The conjecture is the statement below. Since q-(2p+1) = 2^n is an integer, n >= 0. The
difference is taken in natural numbers: it equals 2^n >= 1 only when q > 2p+1, so truncated
subtraction adds no solutions.
-/

namespace OMA.S_oeis_a296806

/-- For every positive integer p there are infinitely many primes q such that q - (2p+1) is a
power of 2. -/
theorem main : ∀ p : ℕ, 0 < p →
    Set.Infinite {q : ℕ | q.Prime ∧ ∃ n : ℕ, q - (2 * p + 1) = 2 ^ n} := by
  sorry

end OMA.S_oeis_a296806
