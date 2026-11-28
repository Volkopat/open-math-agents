import Mathlib

/-!
# A300013: a(n) is the number of primes p such that both 2n-p and 2n+2-nextprime(p) are prime numbers.

Source: https://oeis.org/A300013 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Squee451

Name: a(n) is the number of primes p such that both 2n - p and 2n + 2 - nextprime(p) are prime
numbers, where nextprime(p) stands for the smallest prime number that is greater than p. Offset 1.
Data: 0, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 4, 3, 3, 4, 6, 3, 3, 5, ...

Conjecture (Lei Zhou, in the sequence entry): a(n) > 0 for all integer n > 1.

Conventions:
- `nextPrime p` is the least prime `q` with `p < q`.
- The differences are taken in `ℕ`. Truncated subtraction agrees with the source: `0` is not
  prime, and the programs in the entry count a difference only when it is a positive prime
  (the Mathematica program tests `cp > 0`, and PARI's `isprime` is false on negative numbers).
- `a n` counts with `Set.ncard`. The set is finite, because `(2 * n - p).Prime` forces `p < 2 * n`,
  so `ncard` is the number of such primes and not a junk value.
-/

namespace OMA.S_oeis_a300013

/-- The smallest prime number that is greater than `p`. -/
def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- A300013: the number of primes `p` such that both `2n - p` and `2n + 2 - nextprime(p)` are
prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  {p : ℕ | p.Prime ∧ (2 * n - p).Prime ∧ (2 * n + 2 - nextPrime p).Prime}.ncard

theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a300013
