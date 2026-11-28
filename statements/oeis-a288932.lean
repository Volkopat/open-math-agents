import Mathlib

/-!
# A288932: Fixed point of the mapping 00->1000, 10->10101, starting with 00.

Source: https://oeis.org/A288932
Credit: @agchua

Comment of A288932 (unsigned; the entry is by Clark Kimberling, Jun 25 2017):
  Conjecture: The number of letters (0's and 1's) in the n-th iterate of the mapping is given by
  A123720.
A123720 is a(n) = 2^n + 2^(n-1) - n, with offset 1. The comment counts the iterates as in the
entry's list of the first five iterates (00, 1000, 101011000, ...): the first iterate is the
starting word 00, so the n-th iterate is the word obtained from 00 by n - 1 applications of the
mapping (this is w[n-1] of the entry's Mathematica program, whose line
Table[StringLength[w[n]], {n, 1, 35}] gives 4, 9, 20, 43, ..., that is A123720(n+1)). The claim is
stated for n >= 1, the offset of A123720.
The mapping is applied as in the Mathematica program (StringReplace with the two rules 00->1000
and 10->10101): the word is scanned from the left; if the two letters at the current position are
00 or 10, they are replaced by their image and the scan goes on after them; otherwise (the letters
01 or 11, or a single last letter) the current letter is kept and the scan moves on by one letter.
Letters are Booleans: false is the letter 0 and true is the letter 1.
-/

namespace OMA.S_oeis_a288932

/-- One application of the mapping 00->1000, 10->10101, scanning from the left
(false is 0, true is 1). -/
def step : List Bool → List Bool
  | false :: false :: t => true :: false :: false :: false :: step t
  | true :: false :: t => true :: false :: true :: false :: true :: step t
  | x :: t => x :: step t
  | [] => []

/-- The n-th iterate of the mapping (n >= 1): the first iterate is the word 00. -/
def iter (n : ℕ) : List Bool := step^[n - 1] [false, false]

/-- A123720(n) = 2^n + 2^(n-1) - n. -/
def A123720 (n : ℕ) : ℤ := 2 ^ n + 2 ^ (n - 1) - n

/-- The comment's conjecture: for n >= 1 the n-th iterate has A123720(n) letters. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ((iter n).length : ℤ) = A123720 n := by
  sorry

end OMA.S_oeis_a288932
