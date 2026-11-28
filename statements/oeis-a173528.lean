import Mathlib

/-!
# A173528: a(n) = 1 + sum of digits of n-1 written in base 8.

Source: https://oeis.org/A173528
Credit: @agchua

Comment of A173528 (the entry is by Omar E. Pol, Feb 20 2010), verbatim:
  If A053829 is written as a triangle then the rows converge to this sequence; see the
  conjecture in A000120.
Offset of A173528: 1 (data 1, 2, 3, 4, 5, 6, 7, 8, 2, 3, ...). A053829(m) is the sum of the
base-8 digits of m (offset 0), with A053829(0) = 0. In A053829 the triangle is displayed as
(the third row abbreviated here)
  0,
  1,2,3,4,5,6,7,
  1,2,3,4,5,6,7,8,2,3,4,5,6,7,8,9,3,...,14,
  1,2,3,4,5,6,7,8,2,3,4,5,6,7,8,9,3,4,5,6,7,8,9,10,4,5,6,7,8,9,10...

Formalisation. Row 0 of the triangle is A053829(0) and, for k >= 0, row k+1 is
A053829(8^k), A053829(8^k + 1), ..., A053829(8^(k+1) - 1), a row of length 7*8^k; so entry j of
row k+1 (0 <= j < 7*8^k) is A053829(8^k + j). The rows converge to this sequence means: for
every n >= 1, from some row on, every row has an entry at position n - 1 (counted from 0) and
that entry equals a(n).
-/

namespace OMA.S_oeis_a173528

/-- A053829(m): the sum of the digits of m written in base 8. -/
def A053829 (m : ℕ) : ℕ := (Nat.digits 8 m).sum

/-- A173528, offset 1: a(n) = 1 + sum of digits of n-1 written in base 8. -/
def a (n : ℕ) : ℕ := 1 + A053829 (n - 1)

/-- Entry j of row k+1 of the triangle of A053829 (0 <= j < 7*8^k). -/
def rowEntry (k j : ℕ) : ℕ := A053829 (8 ^ k + j)

/-- The rows of the triangle of A053829 converge to A173528. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    n - 1 < 7 * 8 ^ k ∧ rowEntry k (n - 1) = a n := by
  sorry

end OMA.S_oeis_a173528
