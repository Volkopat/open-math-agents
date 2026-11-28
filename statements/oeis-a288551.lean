import Mathlib

/-!
# A288551: 0-limiting word of the mapping 00->0101, 1->011, starting with 00.

Source: https://oeis.org/A288551
Credit: @agchua

Comment of A288551 (the entry is by Clark Kimberling, Jun 14 2017), verbatim:
  Conjecture: the number of letters (0's and 1's) in the n-th iterate is given by A288476(n).
The iterates are those of the entry's Mathematica program, whose first iterates the entry lists
(00, 0101, 00110011, ...): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 0101, 1 -> 011}]. StringReplace reads the word from the
left; at each position it replaces a block 00 or a letter 1 that starts there and continues
after it, and otherwise (a letter 0 not followed by 0) it keeps the letter and moves on by one.
Words are lists of Booleans, the letter 0 being false and the letter 1 being true.
A288476 (offset 0) is defined in its entry by a(n) = a(n-1) + 4*a(n-2) - 2*a(n-3), where
a(0) = 2, a(1) = 4, a(2) = 8; its values are taken in the integers because of the subtraction.
The n-th iterate is w(n), n >= 0, as A288476 has offset 0 and A288476(0) = 2 is the length of
the starting word 00 (the program's line Table[StringLength[w[n]], {n, 1, 35}], marked A288476
conjectured, gives 4, 8, 20, ..., that is A288476(1), A288476(2), ...).
-/

namespace OMA.S_oeis_a288551

/-- One application of the mapping 00 -> 0101, 1 -> 011 (StringReplace, read from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: true :: false :: true :: step rest
  | true :: rest => false :: true :: true :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A288476: a(n) = a(n-1) + 4*a(n-2) - 2*a(n-3), a(0) = 2, a(1) = 4, a(2) = 8. -/
def A288476 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | n + 3 => A288476 (n + 2) + 4 * A288476 (n + 1) - 2 * A288476 n

/-- The conjecture: the n-th iterate has A288476(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A288476 n := by
  sorry

end OMA.S_oeis_a288551
