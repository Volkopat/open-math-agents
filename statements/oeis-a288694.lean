import Mathlib

/-!
# A288694: Fixed point of the mapping 00->0110, 10->100, starting with 00.

Source: https://oeis.org/A288694
Credit: @agchua

Comment of A288694 (the entry is by Clark Kimberling, Jun 16 2017):
  Conjecture: the number of letters (0's and 1's) in the n-th iterate is given by A288429(n).
The iterates are those of the entry's Mathematica program, whose first iterates the entry lists
(00, 0110, 01100, 011000, 011000110, ...): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 0110, 10 -> 100}]. StringReplace reads the word from the
left; at each position it replaces a block 00 or 10 that starts there and continues after the
block, and otherwise (the letters 01 or 11, or a single last letter) it keeps the letter and
moves on by one. Words are lists of Booleans, the letter 0 being false and the letter 1 being
true. A288429 (offset 0) is defined in its entry by a(n) = 2*a(n-1) - a(n-2) + a(n-3) - a(n-4),
where a(0) = 2, a(1) = 4, a(2) = 5, a(3) = 6; its values are taken in the integers because of
the subtraction. The n-th iterate is w(n), n >= 0, as A288429 has offset 0 and A288429(0) = 2 is
the length of the starting word 00 (the program's line Table[StringLength[w[n]], {n, 1, 35}],
marked A288429 conjectured, gives 4, 5, 6, ..., that is A288429(1), A288429(2), ...).
-/

namespace OMA.S_oeis_a288694

/-- One application of the mapping 00 -> 0110, 10 -> 100 (StringReplace, read from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: true :: true :: false :: step rest
  | true :: false :: rest => true :: false :: false :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A288429. -/
def A288429 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | n + 4 => 2 * A288429 (n + 3) - A288429 (n + 2) + A288429 (n + 1) - A288429 n

/-- The conjecture: the n-th iterate has A288429(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A288429 n := by
  sorry

end OMA.S_oeis_a288694
