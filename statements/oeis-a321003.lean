import Mathlib

/-!
# A321003: a(n) = 2^n*(4*3^n-1).

Source: https://oeis.org/A321003
Credit: @agchua

Comment of A321003 (unsigned; the entry is by N. J. A. Sloane, Nov 01 2018):
  Conjectured to be the sum of A175046(i) for 1 <= i < 2^(n+1).
A175046 (offset 1, by Leroy Quet, Dec 02 2009): Write n in binary, then increase each run of 0's
by one 0, and increase each run of 1's by one 1. a(n) is the decimal equivalent of the result.
The comments of A175046 (Chai Wah Wu, Nov 18 2018) prove that the sum of A175046(i) for
2^k <= i < 2^(k+1) is 3 for k = 0 and 20*6^(k-1) - 2^(k-1) for k > 0; summing these blocks gives
the claim.

Formalisation of A175046: Nat.digits 2 n is the list of binary digits of n, least significant
first (the runs are the same in either reading direction). The function expand copies a list of
digits and writes the last digit of every maximal run of equal digits twice, which increases
every run by one digit of its own kind; Nat.ofDigits 2 reads the result back in base 2. For
example 6 = 110 in binary becomes 11100 = 28. A321003 has offset 0, and the claim is stated for
every n >= 0.
-/

namespace OMA.S_oeis_a321003

/-- Increase each run of equal digits by one digit: a digit that is not followed by an equal digit
(the last digit of its run) is written twice, every other digit once. -/
def expand : List ℕ → List ℕ
  | [] => []
  | x :: t => if t.head? = some x then x :: expand t else x :: x :: expand t

/-- A175046(n): the binary expansion of n with each run increased by one digit, read in base 2. -/
def A175046 (n : ℕ) : ℕ := Nat.ofDigits 2 (expand (Nat.digits 2 n))

/-- A321003: a(n) = 2^n*(4*3^n - 1). -/
def a (n : ℕ) : ℤ := 2 ^ n * (4 * 3 ^ n - 1)

/-- The conjecture: a(n) is the sum of A175046(i) for 1 <= i < 2^(n+1). -/
theorem main : ∀ n : ℕ, a n = ∑ i ∈ Finset.Ico 1 (2 ^ (n + 1)), (A175046 i : ℤ) := by
  sorry

end OMA.S_oeis_a321003
