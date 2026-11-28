import Mathlib

/-!
# A053830: Sum of digits of (n written in base 9).

Source: https://oeis.org/A053830
Credit: @agchua

Example lines of A053830 (the entry is by Henry Bottomley, Mar 28 2000), verbatim:
  From Omar E. Pol, Feb 23 2010: (Start)
  It appears that this can be written as a triangle (see the conjecture in the entry A000120):
    0;
    1,2,3,4,5,6,7,8;
    1,2,3,4,5,6,7,8,9,2,3,4,5,6,7,8,9,10,3,4,5,6,7,8,9,10,11,4,5,6,7,8,9,10,11,...
  where the rows converge to A173529. (End)
A173529 (offset 1), name line: a(n) = 1 + A053830(n-1), where A053830 is the sum of the digits of its argument in base 9.

Formalisation. Offset 0: a(n) is the sum of the base-9 digits of n. The displayed triangle has
row 0 = a(0) and, for k >= 0, row k+1 = a(9^k), a(9^k + 1), ..., a(9^(k+1) - 1), a row of
length 8*9^k; so entry j of row k+1 (0 <= j < 8*9^k) is a(9^k + j). The rows converge to
A173529 means: for every n >= 1, from some row on, every row has an entry at position n - 1
(counted from 0) and that entry equals A173529(n).
-/

namespace OMA.S_oeis_a053830

/-- A053830(n): the sum of the digits of n written in base 9. -/
def a (n : ℕ) : ℕ := (Nat.digits 9 n).sum

/-- Entry j of row k+1 of the triangle (rows a(9^k), ..., a(9^(k+1) - 1), 0 <= j < 8*9^k). -/
def rowEntry (k j : ℕ) : ℕ := a (9 ^ k + j)

/-- A173529(n) = 1 + A053830(n-1), offset 1. -/
def A173529 (n : ℕ) : ℕ := 1 + a (n - 1)

/-- The rows of the triangle converge to A173529. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    n - 1 < 8 * 9 ^ k ∧ rowEntry k (n - 1) = A173529 n := by
  sorry

end OMA.S_oeis_a053830
