import Mathlib

/-!
# A136809: Numbers k such that k and k^2 use only the digits 0, 1, 2 and 3.

Source: https://oeis.org/A136809
Credit: @agchua

Comment of A136809 (M. F. Hasler, Nov 03 2020; the entry is by Jonathan Wellons, Jan 22 2008):
  Conjecture: the sequence contains only binary numbers (digits 0 or 1) having no more than
  three 1's in a row, and not more than one run of two or more consecutive 1's. (But not all
  such numbers, since 101101 for example is not in the sequence.)
(In the entry the words binary numbers stand in double quotes.) The decimal digit of k at
position i, counted from the right starting at 0, is k / 10^i % 10; positions beyond the last
digit give 0, which changes none of the conditions. k is a term when every digit of k and of
k^2 is at most 3. The conjecture is stated as three conditions on every term k: every digit is
0 or 1; no four consecutive digits are 1; and there are no two runs of two or more consecutive
1's, that is, no positions i + 1 < l < j with the digit 1 at i, i + 1, j and j + 1 and a digit
other than 1 at l. The other sentences of the comment (A136813(144) = 31733311 is not a term,
10*k is a term when k is, 101101 is not a term) are facts, not part of the conjecture.
-/

namespace OMA.S_oeis_a136809

/-- The decimal digit of k at position i, counted from the right starting at 0. -/
def digit (k i : ℕ) : ℕ := k / 10 ^ i % 10

/-- k is a term of A136809: k and k^2 use only the digits 0, 1, 2 and 3. -/
def IsTerm (k : ℕ) : Prop := (∀ i : ℕ, digit k i ≤ 3) ∧ (∀ i : ℕ, digit (k ^ 2) i ≤ 3)

/-- The conjecture: every term has only the digits 0 and 1, has no four consecutive 1's, and has
at most one run of two or more consecutive 1's. -/
theorem main : ∀ k : ℕ, IsTerm k →
    (∀ i : ℕ, digit k i ≤ 1) ∧
    (¬ ∃ i : ℕ, digit k i = 1 ∧ digit k (i + 1) = 1 ∧ digit k (i + 2) = 1 ∧
      digit k (i + 3) = 1) ∧
    (¬ ∃ i l j : ℕ, i + 1 < l ∧ l < j ∧ digit k i = 1 ∧ digit k (i + 1) = 1 ∧ digit k l ≠ 1 ∧
      digit k j = 1 ∧ digit k (j + 1) = 1) := by
  sorry

end OMA.S_oeis_a136809
