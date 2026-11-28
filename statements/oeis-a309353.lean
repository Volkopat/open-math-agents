import Mathlib

/-!
# A309353: Let d(1), d(2), ..., d(q) be the q divisors of a number m. The sequence lists the numbers m such that {phi(d(1)), phi(d(2)), ..., phi(d(q))} is the set of the divisors of a number k, where phi is the Euler totient function.

Source: https://oeis.org/A309353
Credit: @agchua

Comment of A309353 (unsigned; the entry is by Michel Lagneau, Aug 02 2019):
  Conjecture: the corresponding numbers k of the sequence is a sequence b(n) of powers of 2.
The terms m of the sequence are positive (offset 1, first term 1). For a term m, the set of the
values phi(d) over the divisors d of m is the set of the divisors of a number k; the conjecture
says that this k is a power of 2. It is stated for every m >= 1 and every k with that property.
-/

namespace OMA.S_oeis_a309353

/-- The conjecture: if {phi(d) : d | m} is the set of the divisors of k, then k is a power of 2. -/
theorem main : ∀ m k : ℕ, 1 ≤ m →
    (Nat.divisors m).image Nat.totient = Nat.divisors k → ∃ i : ℕ, k = 2 ^ i := by
  sorry

end OMA.S_oeis_a309353
