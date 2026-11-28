import Mathlib

/-!
# A053827: Sum of digits of (n written in base 6).

Source: https://oeis.org/A053827
Credit: @agchua

Example lines of A053827 (the entry is by Henry Bottomley, Mar 28 2000), verbatim:
  From Omar E. Pol, Feb 21 2010: (Start)
  It appears that this can be written as a triangle :
    0,
    1,2,3,4,5,
    1,2,3,4,5,6,2,3,4,5,6,7,3,4,5,6,7,8,4,5,6,7,8,9,5,6,7,8,9,10,
    1,2,3,4,5,6,2,3,4,5,6,7,3,4,5,6,7,8,4,5,6,7,8,9,5,6,7,8,9,10,6,7,8,9,10,11,2...
  where the rows converge to A173526.
  See the conjecture in the entry A000120. (End)
A173526 (offset 1), name line: a(n) = 1 + A053827(n-1), where A053827 is the sum-of-digits
function in base 6.

Formalisation. Offset 0: a(n) is the sum of the base-6 digits of n. The displayed triangle has
row 0 = a(0) and, for k >= 0, row k+1 = a(6^k), a(6^k + 1), ..., a(6^(k+1) - 1), a row of
length 5*6^k; so entry j of row k+1 (0 <= j < 5*6^k) is a(6^k + j). The rows converge to
A173526 means: for every n >= 1, from some row on, every row has an entry at position n - 1
(counted from 0) and that entry equals A173526(n).
-/

namespace OMA.S_oeis_a053827

/-- A053827(n): the sum of the digits of n written in base 6. -/
def a (n : ℕ) : ℕ := (Nat.digits 6 n).sum

/-- Entry j of row k+1 of the triangle (rows a(6^k), ..., a(6^(k+1) - 1), 0 <= j < 5*6^k). -/
def rowEntry (k j : ℕ) : ℕ := a (6 ^ k + j)

/-- A173526(n) = 1 + A053827(n-1), offset 1. -/
def A173526 (n : ℕ) : ℕ := 1 + a (n - 1)

/-- The rows of the triangle converge to A173526. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    n - 1 < 5 * 6 ^ k ∧ rowEntry k (n - 1) = A173526 n := by
  sorry

end OMA.S_oeis_a053827
