import Mathlib

/-!
# A053829: Sum of digits of (n written in base 8).

Source: https://oeis.org/A053829
Credit: @agchua

Example lines of A053829 (the entry is by Henry Bottomley, Mar 28 2000), verbatim:
  From Omar E. Pol, Feb 21 2010: (Start)
  It appears that this can be written as a triangle (See the conjecture in the entry A000120):
    0,
    1,2,3,4,5,6,7,
    1,2,3,4,5,6,7,8,2,3,4,5,6,7,8,9,3,4,5,6,7,8,9,10,4,5,6,7,8,9,10,11,5,6,7,8,9,10,11,12,6,7,8,9,10,11,12,13,7,8,9,10,11,12,13,14,
    1,2,3,4,5,6,7,8,2,3,4,5,6,7,8,9,3,4,5,6,7,8,9,10,4,5,6,7,8,9,10...
  where the rows converge to A173528. (End)
A173528 (offset 1), name line: a(n) = 1 + sum of digits of n-1 written in base 8.

Formalisation. Offset 0: a(n) is the sum of the base-8 digits of n. The displayed triangle has
row 0 = a(0) and, for k >= 0, row k+1 = a(8^k), a(8^k + 1), ..., a(8^(k+1) - 1), a row of
length 7*8^k; so entry j of row k+1 (0 <= j < 7*8^k) is a(8^k + j). The rows converge to
A173528 means: for every n >= 1, from some row on, every row has an entry at position n - 1
(counted from 0) and that entry equals A173528(n).
-/

namespace OMA.S_oeis_a053829

/-- A053829(n): the sum of the digits of n written in base 8. -/
def a (n : ℕ) : ℕ := (Nat.digits 8 n).sum

/-- Entry j of row k+1 of the triangle (rows a(8^k), ..., a(8^(k+1) - 1), 0 <= j < 7*8^k). -/
def rowEntry (k j : ℕ) : ℕ := a (8 ^ k + j)

/-- A173528(n) = 1 + A053829(n-1), offset 1. -/
def A173528 (n : ℕ) : ℕ := 1 + a (n - 1)

/-- The rows of the triangle converge to A173528. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    n - 1 < 7 * 8 ^ k ∧ rowEntry k (n - 1) = A173528 n := by
  sorry

end OMA.S_oeis_a053829
