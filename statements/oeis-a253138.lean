import Mathlib

/-!
# OEIS A253138: every prime from the sixth on is the arithmetic mean of two semiprimes

Source: https://oeis.org/A253138 (OEIS Foundation, CC BY-SA 4.0).
Credit: @corentingenton
Formalization: AI-generated with Claude Code (model claude-opus-5-5).

Entry A253138, offset 1: Number of ways to represent the n-th prime as the arithmetic mean of two
semiprimes. Comment: Conjecture: a(n)>0 for n>5.
Example: a(12) = 3 as prime(12) = 37 = (9+65)/2 = (25+49)/2 = (35+39)/2.

Formalization notes:
* A semiprime is a product of two primes, not necessarily distinct, i.e. a number with exactly two
  prime factors counted with multiplicity: `ArithmeticFunction.cardFactors s = 2`.
* prime(n) is the n-th prime with offset 1 (prime(1) = 2), i.e. `Nat.nth Nat.Prime (n - 1)`.
* A representation of p as the mean of two semiprimes is an unordered pair {s, t} of semiprimes
  with s + t = 2p, as in the example (9+65, 25+49, 35+39). The pair s = t = p is impossible since
  p is prime, so a(n) > 0 means that there are semiprimes s < t with s + t = 2 prime(n).
* Controls: counting pairs s < t with s + t = 2p reproduces the 32 data terms
  0, 0, 1, 1, 0, 1, 1, 1, 1, 2, 1, 3, ...; the conjecture starts at n = 6 (prime 13 = (4+22)/2)
  because a(5) = 0 (prime 11).
-/

namespace OMA.S_oeis_a253138

/-- A semiprime: exactly two prime factors counted with multiplicity. -/
def IsSemiprime (s : ℕ) : Prop := ArithmeticFunction.cardFactors s = 2

/-- The conjecture a(n) > 0 for n > 5: the n-th prime is the mean of two semiprimes. -/
theorem main : ∀ n : ℕ, 5 < n → ∃ s t : ℕ, s < t ∧ IsSemiprime s ∧ IsSemiprime t ∧
    s + t = 2 * Nat.nth Nat.Prime (n - 1) := by
  sorry

end OMA.S_oeis_a253138
