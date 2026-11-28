import Mathlib

/-!
# A287530: 1-limiting word of the mapping 00->1000, 10->001, starting with 00.

Source: https://oeis.org/A287530
Credit: @agchua

Comment of A287530 (the entry is by Clark Kimberling, Jun 18 2017), verbatim:
  Conjecture: the number of letters (0's and 1's) in the n-th iterate is given by A287525(n),
  for n >= 0.
The iterates are those of the entry's Mathematica program, whose first iterates the entry lists
(00, 1000, 0011000, 100010011000, ...): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 1000, 10 -> 001}]. StringReplace reads the word from the
left; at each position it replaces a block 00 or 10 that starts there and continues after the
block, and otherwise it keeps the letter and moves on by one. Words are lists of Booleans, the
letter 0 being false and the letter 1 being true.
The entry also says: The 1-limiting word is the limit of the n-th iterates for odd n.
A287525 (offset 0) is defined in its entry by a(n) = a(n-1) + a(n-2) - a(n-3) + a(n-4) + a(n-5)
for n >= 6, where a(0) = 2, a(1) = 4, a(2) = 7, a(3) = 12, a(4) = 19, a(5) = 31; its values are
taken in the integers because of the subtraction. The n-th iterate is w(n), n >= 0, as A287525
has offset 0 and A287525(0) = 2 is the length of the starting word 00.
-/

namespace OMA.S_oeis_a287530

/-- One application of the mapping 00 -> 1000, 10 -> 001 (StringReplace, read from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => true :: false :: false :: false :: step rest
  | true :: false :: rest => false :: false :: true :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A287525: a(0..5) = 2, 4, 7, 12, 19, 31 and
a(n) = a(n-1) + a(n-2) - a(n-3) + a(n-4) + a(n-5) for n >= 6. -/
def A287525 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 12
  | 4 => 19
  | 5 => 31
  | n + 6 =>
    A287525 (n + 5) + A287525 (n + 4) - A287525 (n + 3) + A287525 (n + 2) + A287525 (n + 1)

/-- The conjecture: the n-th iterate has A287525(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A287525 n := by
  sorry

end OMA.S_oeis_a287530
