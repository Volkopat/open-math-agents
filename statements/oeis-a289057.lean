import Mathlib

/-!
# A289057: Fixed point of the mapping 00->0010, 01->010, 10->011, starting with 00.

Source: https://oeis.org/A289057
Credit: @agchua

Comment of A289057 (the entry is by Clark Kimberling, Jun 27 2017), verbatim:
  Conjecture:  the number of letters (0's and 1's) in the n-th iterate of the mapping is given
  by A289060.
The iterates are those of the entry's Mathematica program, whose first eight iterates the entry
lists (00, 0010, 0010011, 00100110101, 00100110100110111, ...): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 0010, 01 -> 010, 10 -> 011}]. StringReplace reads the word
from the left; at each position it replaces a block 00, 01, or 10 that starts there and continues
after the block, and otherwise (the letters 11, or a single last letter) it keeps the letter and
moves on by one. Words are lists of Booleans, the letter 0 being false and the letter 1 being
true. A289060 (offset 0) is defined in its entry by a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for
n >= 8, where a(0) = 2, a(1) = 4, a(2) = 7, a(3) = 11, a(4) = 17, a(5) = 25, a(6) = 36, a(7) = 51;
its values are taken in the integers because of the subtraction. The n-th iterate is w(n), n >= 0,
as A289060 has offset 0, A289060(0) = 2 is the length of the starting word 00, and the program's
line Table[StringLength[w[n]], {n, 0, 20}] (* A289060 *) gives A289060(n) from n = 0.
-/

namespace OMA.S_oeis_a289057

/-- One application of the mapping 00 -> 0010, 01 -> 010, 10 -> 011 (StringReplace, from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: false :: true :: false :: step rest
  | false :: true :: rest => false :: true :: false :: step rest
  | true :: false :: rest => false :: true :: true :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A289060: a(0..7) = 2, 4, 7, 11, 17, 25, 36, 51 and
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n >= 8. -/
def A289060 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 17
  | 5 => 25
  | 6 => 36
  | 7 => 51
  | n + 8 => 3 * A289060 (n + 7) - 3 * A289060 (n + 6) + A289060 (n + 5)

/-- The conjecture: the n-th iterate has A289060(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A289060 n := by
  sorry

end OMA.S_oeis_a289057
