import Mathlib

/-!
# A053828: Sum of digits of (n written in base 7).

Source: https://oeis.org/A053828
Credit: @agchua

Example lines of A053828 (the entry is by Henry Bottomley, Mar 28 2000), verbatim:
  From Omar E. Pol, Feb 21 2010: (Start)
  It appears that this can be written as a triangle (see the conjecture in the entry A000120):
    0,
    1,2,3,4,5,6,
    1,2,3,4,5,6,7,2,3,4,5,6,7,8,3,4,5,6,7,8,9,4,5,6,7,8,9,10,5,6,7,8,9,10,11,6,7,8,9,10,11,12,
    1,2,3,4,5,6,7,2,3,4,5,6,7,8,3,4,5,6,7,8,9,4,5,6,7,8,9,10,5,6,7,8,9,10,11,6,7,8,9,10,11,12,7,8,9,10,11,...
  where the rows converge to A173527. (End)
A173527 (offset 1), name line: a(n) = 1 + A053828(n-1), where A053828 is the sum of digits in base 7.

Formalisation. Offset 0: a(n) is the sum of the base-7 digits of n. The displayed triangle has
row 0 = a(0) and, for k >= 0, row k+1 = a(7^k), a(7^k + 1), ..., a(7^(k+1) - 1), a row of
length 6*7^k; so entry j of row k+1 (0 <= j < 6*7^k) is a(7^k + j). The rows converge to
A173527 means: for every n >= 1, from some row on, every row has an entry at position n - 1
(counted from 0) and that entry equals A173527(n).
-/

namespace OMA.S_oeis_a053828

/-- A053828(n): the sum of the digits of n written in base 7. -/
def a (n : ℕ) : ℕ := (Nat.digits 7 n).sum

/-- Entry j of row k+1 of the triangle (rows a(7^k), ..., a(7^(k+1) - 1), 0 <= j < 6*7^k). -/
def rowEntry (k j : ℕ) : ℕ := a (7 ^ k + j)

/-- A173527(n) = 1 + A053828(n-1), offset 1. -/
def A173527 (n : ℕ) : ℕ := 1 + a (n - 1)

/-- The rows of the triangle converge to A173527. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    n - 1 < 6 * 7 ^ k ∧ rowEntry k (n - 1) = A173527 n := by
  sorry

end OMA.S_oeis_a053828
