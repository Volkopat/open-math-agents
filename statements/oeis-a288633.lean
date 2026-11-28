import Mathlib

/-!
# A288633: Fixed point of the mapping 00->0110, 1->10, starting with 00.

Source: https://oeis.org/A288633
Credit: @agchua

Comment of A288633 (the entry is by Clark Kimberling, Jun 15 2017):
  Conjecture: the number of letters (0's and 1's) in the n-th iterate is given by A288465(n).
The iterates are those of the entry's Mathematica program, whose first iterates the entry lists
(00, 0110, 010100, 0100100110, ...): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 0110, 1 -> 10}]. StringReplace reads the word from the
left; at each position it replaces a block 00 or a letter 1 that starts there and continues
after it, and otherwise (a letter 0 not followed by 0) it keeps the letter and moves on by one.
Words are lists of Booleans, the letter 0 being false and the letter 1 being true.
A288465 (offset 0) is defined in its entry by a(n) = 2*a(n-1) - a(n-4), where a(0) = 2,
a(1) = 4, a(2) = 6, a(3) = 10; its values are taken in the integers because of the subtraction.
The n-th iterate is w(n), n >= 0, as A288465 has offset 0 and A288465(0) = 2 is the length of the
starting word 00 (the listed iterates 00, 0110, 010100, 0100100110 have 2, 4, 6, 10 letters).
-/

namespace OMA.S_oeis_a288633

/-- One application of the mapping 00 -> 0110, 1 -> 10 (StringReplace, read from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: true :: true :: false :: step rest
  | true :: rest => true :: false :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A288465. -/
def A288465 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 6
  | 3 => 10
  | n + 4 => 2 * A288465 (n + 3) - A288465 n

/-- The conjecture: the n-th iterate has A288465(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A288465 n := by
  sorry

end OMA.S_oeis_a288633
