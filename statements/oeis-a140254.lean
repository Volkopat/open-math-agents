import Mathlib

/-!
# A140254: Mobius transform of A014963.

Source: https://oeis.org/A140254
Credit: @agchua

Entry by Gary W. Adamson and Mats Granvik, May 16 2008, Jun 29 2008. Offset 1.

A014963(n) = 1 unless n is a prime or a prime power, when A014963(n) is that prime
(for a prime power n this prime is the least prime factor of n).
A140254 is its Mobius transform: a(n) = Sum_{d | n} mu(n/d) * A014963(d).

Comment lines of the entry, verbatim:
Conjectures relating to the Mobius sequence A008683:
If mu(n) = 0, a(n) = 0.
If mu(n) = 1, (n>1), a(n) = a negative term.
If mu(n) = -1, a(n) = a positive term.
So except for the first term and zero divided by zero we would have mu(n) = -a(n)/abs(a(n)).

The statement: for every n >= 1 the three implications hold, and for every n > 1 with
a(n) /= 0 we have mu(n) = -a(n)/|a(n)| (an exact integer division).
-/

namespace OMA.S_oeis_a140254

/-- A014963: the least prime factor of n if n is a prime power, and 1 otherwise. -/
def A014963 (n : ℕ) : ℕ := if IsPrimePow n then n.minFac else 1

/-- A140254: the Mobius transform of A014963. -/
def a (n : ℕ) : ℤ := ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) * (A014963 d : ℤ)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (ArithmeticFunction.moebius n = 0 → a n = 0) ∧
    (ArithmeticFunction.moebius n = 1 → 1 < n → a n < 0) ∧
    (ArithmeticFunction.moebius n = -1 → 0 < a n) ∧
    (1 < n → a n ≠ 0 → ArithmeticFunction.moebius n = -a n / |a n|) := by
  sorry

end OMA.S_oeis_a140254
