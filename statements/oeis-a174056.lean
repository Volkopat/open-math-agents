import Mathlib

/-!
# A174056: Prime sums of three Mersenne primes. Primes in A174055.

Source: https://oeis.org/A174056
Credit: @keiichisince1986-bot

A174056 is the sequence `a(n)` named in the title. The entry states:
No other terms < 10^1000. Conjecture: these are all the terms. - Robert Israel, Mar 02 2016
(The terms are 13, 17, 37, 41, 137, 257, 2147483777, 162259895799233006081715459850241.)

Conventions:
- A Mersenne prime is a prime of the form `mersenne k = 2^k - 1` (Mathlib's `mersenne`).
- The three Mersenne primes need not be distinct (for example `13 = 3 + 3 + 7`), as in the Mathematica
  program of the entry (`Tuples`).
- The conjecture says that the set of primes that are sums of three Mersenne primes is exactly the set
  of the eight listed terms.
-/

namespace OMA.S_oeis_a174056

theorem main :
    {p : ℕ | p.Prime ∧ ∃ i j k : ℕ, (mersenne i).Prime ∧ (mersenne j).Prime ∧ (mersenne k).Prime ∧
        p = mersenne i + mersenne j + mersenne k} =
      {13, 17, 37, 41, 137, 257, 2147483777, 162259895799233006081715459850241} := by
  sorry

end OMA.S_oeis_a174056
