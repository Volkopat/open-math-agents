import Mathlib

/-!
# A286059: Fixed point of the mapping 00->001, 1->011, starting with 00.

Source: https://oeis.org/A286059
Credit: @agchua

Comment of A286059 (the entry is by Clark Kimberling, Jun 05 2017), verbatim:
  Conjecture:  the number of letters (0's and 1's) in the n-th iterate of the mapping is given
  by A286062.
The iterates are those of the entry's Mathematica program, whose first iterates the entry lists
(00, 001, 001011, 0010110011011, ...): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 001, 1 -> 011}]. StringReplace reads the word from the
left; at each position it replaces a block 00 or a letter 1 that starts there and continues
after it, and otherwise (a letter 0 not followed by 0) it keeps the letter and moves on by one.
Words are lists of Booleans, the letter 0 being false and the letter 1 being true.
A286062 (offset 0) is defined in its entry by a(n) = 2*a(n-1) + a(n-2) - a(n-3), where a(0) = 2,
a(1) = 3, a(2) = 6; its values are taken in the integers because of the subtraction. The n-th
iterate is w(n), n >= 0, as A286062 has offset 0 and A286062(0) = 2 is the length of the starting
word 00 (the program's line Table[StringLength[w[n]], {n, 1, 35}], marked A286062 conjectured,
gives 3, 6, 13, ..., that is A286062(1), A286062(2), ...).
-/

namespace OMA.S_oeis_a286059

/-- One application of the mapping 00 -> 001, 1 -> 011 (StringReplace, read from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: false :: true :: step rest
  | true :: rest => false :: true :: true :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A286062. -/
def A286062 : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | 2 => 6
  | n + 3 => 2 * A286062 (n + 2) + A286062 (n + 1) - A286062 n

/-- The conjecture: the n-th iterate has A286062(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A286062 n := by
  sorry

end OMA.S_oeis_a286059
