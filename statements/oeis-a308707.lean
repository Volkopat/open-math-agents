import Mathlib

/-!
# A308707: a(n) = gcd(n, phi(n) + sigma(n)), where phi is A000010 and sigma is A000203.

Source: https://oeis.org/A308707
Credit: @agchua

Comments of A308707 (the entry is by Juri-Stepan Gerasimov, Jun 18 2019):
  (i) primes m such that a(m-1) is equal to 1: 2, 5, 17, 37, 101, 257, 401, 577, 677, ...
  Conjecture: ALL m are primes of the form i^2 + 1 (see A002496);
and, from Bernard Schott, Jun 23 2019:
  There are distinct families of integers that satisfy a(k) = 1: ...
  (iv) conjecture: k = m^2 with m >= 1: A000290 \ {0}; if m is prime, it's not a conjecture,
  see (i). This conjecture is stronger than the conjecture of the 1st comment.
The sequence has offset 1. The first conjecture says that every prime m with a(m-1) = 1 is of
the form i^2 + 1; the second says that a(m^2) = 1 for every m >= 1. Both are stated. The
families (i) to (iii) of the second comment are stated there as facts, not as conjectures.
Here phi is Nat.totient and sigma(n) is the sum of the divisors of n, ArithmeticFunction.sigma 1.
-/

namespace OMA.S_oeis_a308707

/-- A308707: a(n) = gcd(n, phi(n) + sigma(n)). -/
def a (n : ℕ) : ℕ := Nat.gcd n (Nat.totient n + ArithmeticFunction.sigma 1 n)

/-- The two conjectures of the entry: every prime m with a(m-1) = 1 is of the form i^2 + 1, and
a(m^2) = 1 for every m >= 1. -/
theorem main :
    (∀ m : ℕ, m.Prime → a (m - 1) = 1 → ∃ i : ℕ, m = i ^ 2 + 1) ∧
    (∀ m : ℕ, 1 ≤ m → a (m ^ 2) = 1) := by
  sorry

end OMA.S_oeis_a308707
