import Mathlib

/-!
# A053824: Sum of digits of (n written in base 5).

Source: https://oeis.org/A053824
Credit: @agchua

Example lines of A053824 (the entry is by Henry Bottomley, Mar 28 2000), verbatim:
  From Omar E. Pol, Feb 21 2010: (Start)
  It appears that this can be written as a triangle:
    0,
    1,2,3,4,
    1,2,3,4,5,2,3,4,5,6,3,4,5,6,7,4,5,6,7,8,
    1,2,3,4,5,2,3,4,5,6,3,4,5,6,7,4,5,6,7,8,5,6,7,8,9,2,3,4,5,6,3,4,5,6,7,4,5,...
  See the conjecture in the entry A000120. (End)
The conjecture in A000120 (Gary W. Adamson) is that the binary digit sums can be written as a
triangle where the rows converge to A063787. For base 5 the limit is A173525 (offset 1), whose
name line is: a(n) = 1 + A053824(n-1), where A053824 = sum of digits in base 5.

Formalisation. Offset 0: a(n) is the sum of the base-5 digits of n. The displayed triangle has
row 0 = a(0) and, for k >= 0, row k+1 = a(5^k), a(5^k + 1), ..., a(5^(k+1) - 1), a row of
length 4*5^k; so entry j of row k+1 (0 <= j < 4*5^k) is a(5^k + j). The statement says both
(1) every row k+1 (k >= 0) is an initial segment of the next row, as displayed (the single
entry 0 of row 0 is not an initial segment of row 1, so row 0 is left out), and
(2) the rows converge to A173525: for every n >= 1, from some row on, every row has an entry at
position n - 1 (counted from 0) and that entry equals A173525(n).
-/

namespace OMA.S_oeis_a053824

/-- A053824(n): the sum of the digits of n written in base 5. -/
def a (n : ℕ) : ℕ := (Nat.digits 5 n).sum

/-- Entry j of row k+1 of the triangle (rows a(5^k), ..., a(5^(k+1) - 1), 0 <= j < 4*5^k). -/
def rowEntry (k j : ℕ) : ℕ := a (5 ^ k + j)

/-- A173525(n) = 1 + A053824(n-1), offset 1. -/
def A173525 (n : ℕ) : ℕ := 1 + a (n - 1)

/-- Each row (after row 0) is an initial segment of the next one, and the rows converge to
A173525. -/
theorem main : (∀ k j : ℕ, j < 4 * 5 ^ k → rowEntry (k + 1) j = rowEntry k j) ∧
    ∀ n : ℕ, 1 ≤ n → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      n - 1 < 4 * 5 ^ k ∧ rowEntry k (n - 1) = A173525 n := by
  sorry

end OMA.S_oeis_a053824
