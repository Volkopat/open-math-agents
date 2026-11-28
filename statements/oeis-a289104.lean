import Mathlib

/-!
# A289104: Fixed point of the mapping 00->0010, 01->011, 10->000, starting with 00.

Source: https://oeis.org/A289104
Credit: @agchua

Comment of A289104 (the entry is by Clark Kimberling, Jun 28 2017), verbatim:
  Conjecture: the number of letters (0's and 1's) in the n-th iterate of the mapping is given by
  A289107. For connections to the golden ratio, see A289105 and A289106.
The iterates are those of the entry's Mathematica program, whose first six iterates the entry lists
(00, 0010, 0010000, 001000000100, 0010000001000100110010,
0010000001000100110010011001010000110): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 0010, 01 -> 011, 10 -> 000}]. StringReplace reads the word from
the left; at each position it replaces a block 00, 01, or 10 that starts there and continues after
the block, and otherwise (a letter 1 followed by 1, or a single last letter) it keeps the letter
and moves on by one. Words are lists of Booleans, the letter 0 being false and the letter 1 being
true.
A289107 (offset 0) is defined in its entry by a(n) = 2*a(n-1) - a(n-3) for n >= 5, with a(0) = 2,
a(1) = 4, a(2) = 7, a(3) = 12, a(4) = 22; its values are taken in the integers because of the
subtraction. The n-th iterate is w(n), n >= 0, as A289107 has offset 0 and A289107(0) = 2 is the
length of the starting word 00 (the program's line Table[StringLength[w[n]], {n, 0, 20}], marked
A289107, gives 2, 4, 7, 12, 22, ...).
-/

namespace OMA.S_oeis_a289104

/-- One application of the mapping 00 -> 0010, 01 -> 011, 10 -> 000 (StringReplace, from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: false :: true :: false :: step rest
  | false :: true :: rest => false :: true :: true :: step rest
  | true :: false :: rest => false :: false :: false :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A289107: a(0..4) = 2, 4, 7, 12, 22 and a(n) = 2*a(n-1) - a(n-3) for n >= 5. -/
def A289107 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 12
  | 4 => 22
  | n + 5 => 2 * A289107 (n + 4) - A289107 (n + 2)

/-- The conjecture: the n-th iterate has A289107(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A289107 n := by
  sorry

end OMA.S_oeis_a289104
