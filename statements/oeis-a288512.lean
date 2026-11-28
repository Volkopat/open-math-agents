import Mathlib

/-!
# A288512: 1-limiting word of the mapping 00->0101, 10->001, starting with 00.

Source: https://oeis.org/A288512
Credit: @agchua

Comment of A288512 (the entry is by Clark Kimberling, Jun 12 2017), verbatim:
  Conjecture: the number of letters (0's and 1's) in the n-th iterate is given by A288511(n).
The iterates are those of the entry's Mathematica program, whose first iterates the entry lists
(00, 0101, 00011, 0101011, 000100111, ...): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 0101, 10 -> 001}]. StringReplace reads the word from the
left; at each position it replaces a block 00 or 10 that starts there and continues after the
block, and otherwise it keeps the letter and moves on by one. Words are lists of Booleans, the
letter 0 being false and the letter 1 being true.
A288511 (offset 0) is defined in its entry by a(n) = 2*a(n-1) - a(n-2) + 2*a(n-3) - 4*a(n-4)
+ 4*a(n-5) - 4*a(n-6) + 4*a(n-7) - 4*a(n-8) + 4*a(n-9) - 3*a(n-10) + 2*a(n-11) - 3*a(n-12)
+ 2*a(n-13) for n >= 16, with the initial values a(0), ..., a(15) = 2, 4, 5, 7, 9, 12, 17, 23,
33, 48, 70, 103, 152, 228, 343, 515 shown in its data; its values are taken in the integers
because of the subtraction. The n-th iterate is w(n), n >= 0, as A288511 has offset 0 and
A288511(0) = 2 is the length of the starting word 00 (the program's line
Table[StringLength[w[n]], {n, 1, 35}], marked A288511 conjectured, gives 4, 5, 7, 9, ..., that
is A288511(1), A288511(2), ...).
-/

namespace OMA.S_oeis_a288512

/-- One application of the mapping 00 -> 0101, 10 -> 001 (StringReplace, read from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: true :: false :: true :: step rest
  | true :: false :: rest => false :: false :: true :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A288511: the initial values a(0..15) and
a(n) = 2*a(n-1) - a(n-2) + 2*a(n-3) - 4*a(n-4) + 4*a(n-5) - 4*a(n-6) + 4*a(n-7) - 4*a(n-8)
+ 4*a(n-9) - 3*a(n-10) + 2*a(n-11) - 3*a(n-12) + 2*a(n-13) for n >= 16. -/
def A288511 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 7
  | 4 => 9
  | 5 => 12
  | 6 => 17
  | 7 => 23
  | 8 => 33
  | 9 => 48
  | 10 => 70
  | 11 => 103
  | 12 => 152
  | 13 => 228
  | 14 => 343
  | 15 => 515
  | n + 16 =>
    2 * A288511 (n + 15) - A288511 (n + 14) + 2 * A288511 (n + 13) - 4 * A288511 (n + 12) +
      4 * A288511 (n + 11) - 4 * A288511 (n + 10) + 4 * A288511 (n + 9) - 4 * A288511 (n + 8) +
      4 * A288511 (n + 7) - 3 * A288511 (n + 6) + 2 * A288511 (n + 5) - 3 * A288511 (n + 4) +
      2 * A288511 (n + 3)

/-- The conjecture: the n-th iterate has A288511(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A288511 n := by
  sorry

end OMA.S_oeis_a288512
