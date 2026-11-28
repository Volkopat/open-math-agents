import Mathlib

/-!
# A288524: 1-limiting word of the mapping 00->0101, 10->010, starting with 00.

Source: https://oeis.org/A288524
Credit: @agchua

Comment of A288524 (the entry is by Clark Kimberling, Jun 14 2017), verbatim:
  Conjecture: the number of letters (0's and 1's) in the n-th iterate is given by A288523(n).
The iterates are those of the entry's Mathematica program, whose first iterates the entry lists
(00, 0101, 00101, 01010101, ...): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 0101, 10 -> 010}]. StringReplace reads the word from the
left; at each position it replaces a block 00 or 10 that starts there and continues after the
block, and otherwise it keeps the letter and moves on by one. Words are lists of Booleans, the
letter 0 being false and the letter 1 being true.
A288523 (offset 0) is defined in its entry by a(n) = a(n-1) + a(n-2) + a(n-3) - 2*a(n-4) for
n >= 5, where a(0) = 2, a(1) = 4, a(2) = 5, a(3) = 8, a(4) = 11; its values are taken in the
integers because of the subtraction. The n-th iterate is w(n), n >= 0, as A288523 has offset 0
and A288523(0) = 2 is the length of the starting word 00 (the program's line
Table[StringLength[w[n]], {n, 1, 35}], marked A288523 conjectured, gives 4, 5, 8, 11, ..., that
is A288523(1), A288523(2), ...).
-/

namespace OMA.S_oeis_a288524

/-- One application of the mapping 00 -> 0101, 10 -> 010 (StringReplace, read from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: true :: false :: true :: step rest
  | true :: false :: rest => false :: true :: false :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A288523: a(0..4) = 2, 4, 5, 8, 11 and a(n) = a(n-1) + a(n-2) + a(n-3) - 2*a(n-4) for
n >= 5. -/
def A288523 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 8
  | 4 => 11
  | n + 5 => A288523 (n + 4) + A288523 (n + 3) + A288523 (n + 2) - 2 * A288523 (n + 1)

/-- The conjecture: the n-th iterate has A288523(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A288523 n := by
  sorry

end OMA.S_oeis_a288524
