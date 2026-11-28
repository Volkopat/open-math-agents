import Mathlib

/-!
# A289239: Fixed point of the mapping 00->0010, 01->100, 10->010, starting with 00.

Source: https://oeis.org/A289239
Credit: @agchua

Comment of A289239 (the entry is by Clark Kimberling, Jun 29 2017), verbatim:
  Conjecture: the number of letters (0's and 1's) in the n-th iterate of the mapping is given by
  A289004.
The iterates are those of the entry's Mathematica program, whose first six iterates the entry lists
(00, 0010, 0010010, 00100101000, 001001010010000100, 0010010100100001001000101000010): w(0) = 00
and w(n) = StringReplace[w(n-1), {00 -> 0010, 01 -> 100, 10 -> 010}]. StringReplace reads the word
from the left; at each position it replaces a block 00, 01, or 10 that starts there and continues
after the block, and otherwise (a letter 1 followed by 1, or a single last letter) it keeps the
letter and moves on by one. Words are lists of Booleans, the letter 0 being false and the letter 1
being true.
A289004 (offset 0) is defined in its entry by
a(n) = 2*a(n-1) - a(n-2) + 2*a(n-4) - a(n-5) + a(n-7) - a(n-8) - a(n-10) for n >= 10, with initial
values a(0..9) = 2, 4, 7, 11, 18, 31, 52, 89, 151, 257 (the entry's prose prints a(9) = 151,
a(9) = 257 for a(8) = 151, a(9) = 257, as confirmed by its data, generating function, and
LinearRecurrence program); its values are taken in the integers because of the subtraction. The
n-th iterate is w(n), n >= 0, as A289004 has offset 0 and A289004(0) = 2 is the length of the
starting word 00 (the program's line Table[StringLength[w[n]], {n, 0, 20}], marked A289004
conjectured, gives 2, 4, 7, 11, 18, 31, ...).
-/

namespace OMA.S_oeis_a289239

/-- One application of the mapping 00 -> 0010, 01 -> 100, 10 -> 010 (StringReplace, from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: false :: true :: false :: step rest
  | false :: true :: rest => true :: false :: false :: step rest
  | true :: false :: rest => false :: true :: false :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A289004: a(0..9) = 2, 4, 7, 11, 18, 31, 52, 89, 151, 257 and
a(n) = 2*a(n-1) - a(n-2) + 2*a(n-4) - a(n-5) + a(n-7) - a(n-8) - a(n-10) for n >= 10. -/
def A289004 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 18
  | 5 => 31
  | 6 => 52
  | 7 => 89
  | 8 => 151
  | 9 => 257
  | n + 10 =>
    2 * A289004 (n + 9) - A289004 (n + 8) + 2 * A289004 (n + 6) - A289004 (n + 5) +
      A289004 (n + 3) - A289004 (n + 2) - A289004 n

/-- The conjecture: the n-th iterate has A289004(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A289004 n := by
  sorry

end OMA.S_oeis_a289239
