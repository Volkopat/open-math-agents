import Mathlib

/-!
# A249761: Primes p such that there is prime q with sigma(q-1) = p.

Source: https://oeis.org/A249761
Credit: @keiichisince1986-bot

A249761 is the sequence `a(n)` named in the title. The entry states:
Conjectures: 1) sequence is finite; 2) (a(n)+3)/2 is a Fermat prime (A019434); 3) a(n) is
subsequence of Mersenne primes (A000668); 4) a(n) = 2*A249759(n)-3. [Only conjecture 1, that the
sequence is finite, is formalized here.]

Conventions:
- `sigma` is `ArithmeticFunction.sigma 1`. For `q = 2`, `sigma(1) = 1` is not prime, and for `q ≥ 2` the
  natural-number subtraction `q - 1` is exact.
- The sequence is the set of primes `p` such that `sigma(q - 1) = p` for some prime `q`; the conjecture
  says this set is finite.
-/

namespace OMA.S_oeis_a249761

theorem main :
    {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ ArithmeticFunction.sigma 1 (q - 1) = p}.Finite := by
  sorry

end OMA.S_oeis_a249761
