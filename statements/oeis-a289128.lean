import Mathlib

/-!
# A289128: Fixed point of the mapping 00->0010, 01->011, 10->010, starting with 00.

Source: https://oeis.org/A289128
Credit: @agchua

Comment of A289128 (the entry is by Clark Kimberling, Jun 28 2017), verbatim:
  Conjecture: the number of letters (0's and 1's) in the n-th iterate of the mapping is given by
  A289131.
The iterates are those of the entry's Mathematica program, whose first six iterates the entry lists
(00, 0010, 0010010, 00100100110, 001001001100101010, 0010010011001010100110110110): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 0010, 01 -> 011, 10 -> 010}]. StringReplace reads the word from
the left; at each position it replaces a block 00, 01, or 10 that starts there and continues after
the block, and otherwise (a letter 1 followed by 1, or a single last letter) it keeps the letter
and moves on by one. Words are lists of Booleans, the letter 0 being false and the letter 1 being
true.
A289131 (offset 0) is defined in its entry by
a(n) = a(n-1) + 3*a(n-2) - 3*a(n-3) - 2*a(n-4) + 2*a(n-5) for n >= 6, with a(0) = 2, a(1) = 4,
a(2) = 7, a(3) = 11, a(4) = 18, a(5) = 28; its values are taken in the integers because of the
subtraction. The n-th iterate is w(n), n >= 0, as A289131 has offset 0 and A289131(0) = 2 is the
length of the starting word 00 (the program's line Table[StringLength[w[n]], {n, 0, 20}], marked
A289131 conjectured, gives 2, 4, 7, 11, 18, 28, ...).
-/

namespace OMA.S_oeis_a289128

/-- One application of the mapping 00 -> 0010, 01 -> 011, 10 -> 010 (StringReplace, from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: false :: true :: false :: step rest
  | false :: true :: rest => false :: true :: true :: step rest
  | true :: false :: rest => false :: true :: false :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A289131: a(0..5) = 2, 4, 7, 11, 18, 28 and
a(n) = a(n-1) + 3*a(n-2) - 3*a(n-3) - 2*a(n-4) + 2*a(n-5) for n >= 6. -/
def A289131 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 18
  | 5 => 28
  | n + 6 =>
    A289131 (n + 5) + 3 * A289131 (n + 4) - 3 * A289131 (n + 3) - 2 * A289131 (n + 2) +
      2 * A289131 (n + 1)

/-- The conjecture: the n-th iterate has A289131(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A289131 n := by
  sorry

end OMA.S_oeis_a289128
